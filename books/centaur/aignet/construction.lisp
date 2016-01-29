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
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
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

(local (in-theory (disable BITOPS::commutativity-of-b-xor
                           BITOPS::BXOR-TO-BNOT
                           BITOPS::BXOR-TO-ID
                           BITOPS::B-AND-EQUAL-1-IN-HYP)))

(local (acl2::use-trivial-ancestors-check))

(defsection simplify-gate

;  (local (include-book "bit-lemmas"))

  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::bfix-when-not-bitp
                             id-eval
                             equal-of-to-lit-backchain
                             o<)))

  (define two-id-measure ((x natp) (y natp))
    :returns (meas o-p)
    :prepwork ((local (in-theory (enable natp))))
    (let ((x (nfix x))
          (y (nfix y)))
      (acl2::two-nats-measure
       (+ 1 (max x y))
       (+ 1 (min x y))))
    ///
    (defthm two-id-measure-symm
      (equal (two-id-measure id1 id2)
             (two-id-measure id2 id1)))

    (local (in-theory (enable aignet-idp)))

    (defthm two-id-measure-of-gate
      (implies (and (equal (id->type id1 aignet) (gate-type))
                    (aignet-idp id1 aignet))
               (b* (((cons node rest) (lookup-id id1 aignet))
                    (ch1 (aignet-lit-fix (gate-node->fanin0 node) rest))
                    (ch2 (aignet-lit-fix (gate-node->fanin1 node) rest)))
                 (and (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch2))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id2 id1))
                      (o< (two-id-measure id2 (lit-id ch2))
                          (two-id-measure id2 id1))))))

    (defthm two-id-measure-of-out
      (implies (and (aignet-nodes-ok aignet)
                    (equal (id->type id1 aignet) (out-type))
                    (aignet-idp id1 aignet))
               (b* (((cons node rest) (lookup-id id1 aignet))
                    (ch1 (aignet-lit-fix (co-node->fanin node) rest)))
                 (and (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id2 id1)))))))

  (define aignet-gate-simp-order ((lit1 litp)
                                  (lit2 litp)
                                  aignet)
    (declare (type (integer 0 *) lit1)
             (type (integer 0 *) lit2))
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet))
    :returns (mv (lit1 litp)
                 (lit2 litp)
                 both neither)
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (gatep1 (int= (id->type id1 aignet) (gate-type)))
         (gatep2 (int= (id->type id2 aignet) (gate-type)))
         ((mv lit1 lit2 both neither)
          (if gatep1
              (if gatep2
                  (mv lit1 lit2 t nil)
                (mv lit1 lit2 nil nil))
            (if gatep2
                (mv lit2 lit1 nil nil)
              (mv lit1 lit2 nil t))))
         ((when (and (not both) (not neither)))
          (mv lit1 lit2 nil nil))
         ((mv lit1 lit2)
          (if (< id2 id1)
              (mv lit2 lit1)
            (mv lit1 lit2))))
      (mv lit1 lit2 both neither))
    ///
    (local (in-theory (enable aignet-gate-simp-order)))

    (defcong lit-equiv equal (aignet-gate-simp-order lit1 lit2 aignet) 1)
    (defcong lit-equiv equal (aignet-gate-simp-order lit1 lit2 aignet) 2)
    (defcong list-equiv equal (aignet-gate-simp-order lit1 lti2 aignet) 3)

    (defthm aignet-gate-simp-order-flags1
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal neither
               (not (equal (id->type (lit-id nlit1) aignet) (gate-type))))))

    (defthm aignet-gate-simp-order-flags2
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal both
               (equal (id->type (lit-id nlit2) aignet) (gate-type)))))

    (defthm aignet-gate-simp-order-flags3
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (implies (not (equal (id->type (lit-id nlit1) aignet) (gate-type)))
                 (not (equal (id->type (lit-id nlit2) aignet) (gate-type))))))

    (defthm two-id-measure-of-aignet-gate-simp-order
      (b* (((mv nlit1 nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (and (equal (two-id-measure (lit-id nlit1) (lit-id nlit2))
                    (two-id-measure (lit-id lit1) (lit-id lit2)))
             (equal (two-id-measure (lit-id nlit2) (lit-id nlit1))
                    (two-id-measure (lit-id lit1) (lit-id lit2)))))
      :hints(("Goal" :in-theory (enable two-id-measure))))

    (defmvtypes aignet-gate-simp-order (natp natp))

    (defthm fanin-precedes-gate-of-aignet-gate-simp-order
      (implies (and (< (lit-id lit1) ngates)
                    (< (lit-id lit2) ngates)
                    (natp ngates))
               (b* (((mv nlit1 nlit2 ?both ?neither)
                     (aignet-gate-simp-order lit1 lit2 aignet)))
                 (and (< (lit-id nlit1) ngates)
                      (< (lit-id nlit2) ngates))))
      :rule-classes (:rewrite :linear))

    (defthm eval-and-of-lits-of-aignet-gate-simp-order
      (b* (((mv nlit1 nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal (eval-and-of-lits nlit1 nlit2 aignet-invals aignet-regvals aignet)
               (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals aignet)))
      :hints(("Goal" :in-theory (enable eval-and-of-lits))))


    ;; (defthmd aignet-gate-simp-order-frame
    ;;   (implies
    ;;    (and (not (equal (nfix n) *num-nodes*))
    ;;         (not (equal (nfix n) *nodesi*)))
    ;;    (equal (let ((aignet (update-nth n v aignet)))
    ;;             (aignet-gate-simp-order lit1 lit2 aignet))
    ;;           (aignet-gate-simp-order lit1 lit2 aignet))))
    ;; (acl2::add-to-ruleset aignet-frame-thms aignet-gate-simp-order-frame)


    ;; (defthm faninp-of-aignet-gate-simp-order
    ;;   (b* (((mv nlit1 nlit2 ?both ?neither)
    ;;         (aignet-gate-simp-order lit1 lit2 aignet)))
    ;;     (implies (and (not (equal (id->type (lit-id lit1) aignet) (out-type)))
    ;;                   (not (equal (id->type (lit-id lit2) aignet) (out-type))))
    ;;              (let ((nodes (nth *nodesi* aignet)))
    ;;                (and (not (equal (node->type (nth-node (lit-id nlit1) nodes)) (out-type)))
    ;;                     (not (equal (node->type (nth-node (lit-id nlit2) nodes))
    ;;                                 (out-type))))))))

    (defthm aignet-litp-of-aignet-gate-simp-order
      (implies (and (aignet-litp lit1 aignet)
                    (aignet-litp lit2 aignet))
               (b* (((mv nlit1 nlit2 ?both ?neither)
                     (aignet-gate-simp-order lit1 lit2 aignet)))
                 (and (aignet-litp nlit1 aignet)
                      (aignet-litp nlit2 aignet))))))



  ;; takes arguments lit1, lit2, and returns:
  ;; (mv exists flg nlit1 nlit2).
  ;;  - if exists is nonnil, it is an in-bounds literal equivalent to lit1 & lit2
  ;;  - otherwise if flg is t, then nlit1, nlit2 are in-bounds and
  ;;       nlit1 & nlit2 === lit1 & lit2
  ;;  - otherwise no simplification was found.
  (acl2::deffunmac
   def-gate-simp (name body
                       &key extra-args
                       (guard 't)
                       (reqs 'nil)
                       (eval-hints 'nil)
                       (fanin-hints 'nil)
; (bounds-hints 'nil)
                       (guard-hints 'nil)
                       (measure-hints 'nil)
                       (skip-measure 'nil)
                       (aignet-litp-hints 'nil)
                       (lit-cong1-hints 'nil)
                       (lit-cong2-hints 'nil)
                       (list-cong-hints 'nil)
; (nth-cong-hints 'nil)
                       (xargs 'nil))
   `(define ,name ((lit1 litp)
                   (lit2 litp)
                   ,@extra-args
                   aignet)
      (declare (type (integer 0 *) lit1)
               (type (integer 0 *) lit2)
               (xargs . ,xargs))
      :guard (and (fanin-litp lit1 aignet)
                  (fanin-litp lit2 aignet)
                  ,guard)
      :guard-hints ,guard-hints
      ,body
      ///
      (local (in-theory (enable ,name)))

      (defmvtypes ,name (nil nil natp natp))

      (defthm ,(mksym name (symbol-name name) "-TYPE")
        (or (not (mv-nth 0 (,name lit1 lit2 ,@extra-args aignet)))
            (natp (mv-nth 0 (,name lit1 lit2 ,@extra-args aignet))))
        :rule-classes :type-prescription)

      ;; (def-aignet-frame ,name
      ;;   ,@(and frame-hints `(:hints ,frame-hints)))

      ;; (defthmd ,(mksym name (symbol-name name) "-FRAME")
      ;;   (implies
      ;;    (and (not (equal (nfix n) *num-nodes*))
      ;;         (not (equal (nfix n) *nodesi*)))
      ;;    (equal (let ((aignet (update-nth n v aignet)))
      ;;             (,name lit1 lit2 ,@extra-args aignet))
      ;;           (,name lit1 lit2 ,@extra-args aignet)))
      ;;   :hints ,(or frame-hints
      ;;               '(("Goal" :in-theory (enable* aignet-frame-thms)))))

      ;; (add-to-ruleset aignet-frame-thms
      ;;                 ,(mksym name (symbol-name name) "-FRAME"))

      (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 1
        :hints ,lit-cong1-hints)
      (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 2
        :hints ,lit-cong2-hints)
      (defcong list-equiv equal (,name lit1 lit2 ,@extra-args aignet)
        ,(+ 3 (len extra-args))
        :hints ,list-cong-hints)

      (defthm ,(mksym name "FANIN-PRECEDES-GATE-OF-" (symbol-name name))
        (implies (and (< (lit-id lit1) gate)
                      (< (lit-id lit2) gate)
                      ;; (aignet-litp lit1 aignet)
                      ;; (aignet-litp lit2 aignet)
                      (natp gate)
                      . ,reqs)
                 (b* (((mv extra ?flg nlit1 nlit2)
                       (,name lit1 lit2 ,@extra-args aignet)))
                   (and (implies extra
                                 (< (lit-id extra) gate))
                        (< (lit-id nlit1) gate)
                        (< (lit-id nlit2) gate))))
        :hints ,fanin-hints
        :rule-classes (:rewrite))

      ,@(and
         (not skip-measure)
         `((defthm ,(mksym name "TWO-ID-MEASURE-OF-" (symbol-name name))
             (implies (and ;; (aignet-litp lit1 aignet)
                           ;; (aignet-litp lit2 aignet)
                           . ,reqs)
                      (b* (((mv ?extra flg nlit1 nlit2)
                            (,name lit1 lit2 ,@extra-args aignet)))
                        (implies flg
                                 (o< (two-id-measure (lit-id nlit1)
                                                     (lit-id nlit2))
                                     (two-id-measure (lit-id lit1)
                                                     (lit-id lit2))))))
             :hints ,measure-hints)))

      (defthm ,(mksym name "AIGNET-LITP-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (implies (and (aignet-litp lit1 aignet)
                        (aignet-litp lit2 aignet)
                        . ,reqs)
                   (and (implies extra
                                 (aignet-litp extra aignet))
                        (aignet-litp nlit1 aignet)
                        (aignet-litp nlit2 aignet))))
        :hints ,aignet-litp-hints)


      (defthm ,(mksym name "EVAL-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (implies (and ;; (aignet-litp lit1 aignet)
                        ;; (aignet-litp lit2 aignet)
                        . ,reqs)
                   (and (implies extra
                                 (equal (lit-eval extra aignet-invals aignet-regvals aignet)
                                        (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals
                                                          aignet)))
                        (equal (eval-and-of-lits nlit1 nlit2 aignet-invals aignet-regvals aignet)
                               (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals aignet)))))
        :hints ,eval-hints)

      (defthm ,(mksym name "LITP-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (and (implies extra
                        (litp extra))
               (litp nlit1)
               (litp nlit2))))))


  (local (in-theory (disable len
                             acl2::nth-with-large-index)))

  ;; (defthmd bits-equal-of-logxor
  ;;   (implies (and (bitp c)
  ;;                 (bitp b)
  ;;                 (bitp a))
  ;;            (equal (equal c (logxor a b))
  ;;                   (equal (equal c 1) (xor (equal a 1) (equal b 1)))))
  ;;   :hints(("Goal" :in-theory (enable bitp))))

  ;; (defthmd bits-equal-of-logand
  ;;   (implies (and (bitp c)
  ;;                 (bitp b)
  ;;                 (bitp a))
  ;;            (equal (equal c (logand a b))
  ;;                   (equal (equal c 1) (and (equal a 1) (equal b 1)))))
  ;;   :hints(("Goal" :in-theory (enable bitp))))

  ;; (defthm logand-of-same
  ;;   (equal (logand a a)
  ;;          (ifix a))
  ;;   :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
  ;;                                      acl2::ihsext-recursive-redefs))))

  ;; (defthm lognot-lognot
  ;;   (equal (lognot (lognot x))
  ;;          (ifix x))
  ;;   :hints(("Goal" :in-theory (enable lognot))))

  ;; (defthm logxor-of-a-a-b
  ;;   (equal (logxor a a b)
  ;;          (ifix b))
  ;;   :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions
  ;;                                    acl2::ihsext-recursive-redefs)
  ;;                                   (acl2::logcdr-natp
  ;;                                    logxor-of-naturals)))))

  ;; (defthm bit-logand-1
  ;;   (implies (bitp a)
  ;;            (equal (logand 1 a)
  ;;                   a))
  ;;   :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
  ;;                                      acl2::ihsext-recursive-redefs))))

  (defthm b-xor-a-a-b
    (equal (b-xor a (b-xor a b))
           (acl2::bfix b))
    :hints(("Goal" :in-theory (enable b-xor acl2::bfix))))

  (defthm b-and-of-xor-not
    (equal (b-and (b-xor (b-not a) b)
                  (b-xor a b))
           0)
    :hints(("Goal" :in-theory (enable b-and b-xor b-not))))

  (def-gate-simp aignet-gate-simp-level1
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((when (int= (id->type (lit-id lit1) aignet) (const-type)))
          (mv (if (int= (lit-neg lit1) 1)
                  lit2    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (int= (id->type (lit-id lit2) aignet) (const-type)))
          (mv (if (int= (lit-neg lit2) 1)
                  lit1    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (= lit1 lit2))
          (mv lit1 nil lit1 lit2))       ;; idempotence
         ((when (= lit1 (lit-negate lit2)))
          (mv 0 nil lit1 lit2)))         ;; contradiction
      (mv nil nil lit1 lit2))
    :eval-hints (("Goal" :in-theory (e/d* (eval-and-of-lits
                                           id-eval lit-eval
                                           equal-of-mk-lit
                                           acl2::arith-equiv-forwarding)))))

  (defund aignet-gate-simp-l2-step1-cond (a b c)
    (or (= a c) (= b c)))


  ;; (local (Defthm lit-eval-of-mk-lit
  ;;          (equal (lit-eval (mk-lit (lit-id lit) neg) aignet-invals aignet-regvals aignet)
  ;;                 (b-xor (b-xor neg (lit-neg lit))
  ;;                        (lit-eval lit aignet-invals aignet-regvals aignet)))
  ;;          :hints(("Goal" :in-theory (enable lit-eval)))))

  (def-gate-simp aignet-gate-simp-l2-step1
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (lit2b (lit-negate lit2))
         (res (or (and (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2b)
                            :exec (or (= a lit2b)
                                      (= b lit2b)))
                       (if (int= (lit-neg lit1) 1)
                           lit2 ;; subsumption1
                         0))    ;; contradiction1
                  (and (int= (lit-neg lit1) 0)
                       (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2)
                            :exec (or (= a lit2) (= b lit2)))
                       lit1))))  ;; idempotence1
      (mv res nil lit1 lit2))
    :guard (int= (id->type (lit-id lit1) aignet) (gate-type))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step1-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-of-lits lit-eval
                                                           equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((id-eval (lit-id lit1) aignet-invals aignet-regvals aignet)
                                 (:free (a b c) (aignet-gate-simp-l2-step1-cond a b
                                                                                c)))))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not
                                               lit-eval))))))

  (defund aignet-gate-simp-l2-step2-cond (a b cb db)
    (or (= a cb)
        (= a db)
        (= b cb)
        (= b db)))


  (local (defthmd lit-eval-open
           (equal (lit-eval lit aignet-invals aignet-regvals aignet)
                  (b-xor (lit-neg lit)
                         (id-eval (lit-id lit) aignet-invals aignet-regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defthmd eval-and-open
           (equal (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals aignet)
                  (b-and (lit-eval lit1 aignet-invals aignet-regvals aignet)
                         (lit-eval lit2 aignet-invals aignet-regvals aignet)))
           :hints(("Goal" :in-theory (enable eval-and-of-lits)))))


  (local (defthmd equal-0-of-lit-neg
           (equal (equal (lit-neg x) 0)
                  (not (equal (lit-neg x) 1)))))

  (local (defthmd equal-0-of-lit-neg-2
           (equal (equal 0 (lit-neg x))
                  (not (equal (lit-neg x) 1)))))

  (local (defun rewriting-negative-literal-equiv (equiv x y mfc state)
           (declare (xargs :mode :program :stobjs state))
           (or (acl2::rewriting-negative-literal-fn `(,equiv ,x ,y) mfc state)
               (acl2::rewriting-negative-literal-fn `(,equiv ,y ,x) mfc state))))

  (local (defthmd equal-of-mk-lit-neg
           (implies (syntaxp
                     (rewriting-negative-literal-equiv
                      'equal x `(mk-lit$inline ,id ,neg) mfc state))
                    (equal (equal x (mk-lit id neg))
                           (and (litp x)
                                (equal (lit-id x) (nfix id))
                                (equal (lit-neg x) (bfix neg)))))
           :hints(("Goal" :in-theory (enable equal-of-mk-lit)))))

  (local (defthm bfix-of-lit-neg
           (Equal (bfix (lit-neg x)) (lit-neg x))))

  ;; (defund and* (x y) (and x y))
  ;; (defthmd equal-of-mk-lit-abbrev
  ;;   (equal (equal a (mk-lit id neg))
  ;;          (and* (litp a)
  ;;                (and* (equal (id-val (lit-id a)) (id-val id))
  ;;                      (equal (lit-neg a) (bfix neg)))))
  ;;   :hints(("Goal" :in-theory (enable equal-of-mk-lit and*))))

  ;; (defthm bitp-norm-equal-to-1
  ;;   (implies (bitp x)
  ;;            (equal (equal x 0)
  ;;                   (equal (b-not x) 1)))
  ;;   :hints(("Goal" :in-theory (enable bitp b-not))))

  (def-gate-simp aignet-gate-simp-l2-step2
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (negp1 (int= (lit-neg lit1) 1))
         (negp2 (int= (lit-neg lit2) 1))
         (cb (lit-negate c))
         (db (lit-negate d))
         (res (and (int= 0 (b-and (lit-neg lit1) (lit-neg lit2)))
                   (mbe :logic (aignet-gate-simp-l2-step2-cond a b cb db)
                        :exec (or (= a cb)
                                  (= a db)
                                  (= b cb)
                                  (= b db)))
                   (cond (negp1 lit2)   ;; subsumption2
                         (negp2 lit1)   ;; subsumption2
                         (t     0)))))  ;; contradiction2
      (mv res nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step2-cond)))
    :fanin-hints (("goal" :in-theory nil)
                  (and stable-under-simplificationp
                       '(:in-theory (enable))))
    :eval-hints (("goal" :in-theory nil)
                 (and stable-under-simplificationp
                      '(:expand ((id-eval (lit-id lit1) aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit2) aignet-invals aignet-regvals aignet)
                                 (:free (a b cb db)
                                  (aignet-gate-simp-l2-step2-cond a b cb
                                                                  db)))
                        :in-theory (e/d (lit-eval-open
                                         eval-and-open
                                         equal-of-mk-lit-neg)
                                        (id-eval))))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor
                                         b-and
                                         b-not))))))

  (defund aignet-gate-simp-l2-step3-cond (a b c d cb db)
    (or (and (= a d) (= b cb))
        (and (= a c) (= b db))))

  (def-gate-simp aignet-gate-simp-l2-step3
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((unless (int= 1 (b-and (lit-neg lit1)
                                 (lit-neg lit2))))
          (mv nil nil lit1 lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (cb (lit-negate c))
         (db (lit-negate d))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond a b c d cb db)
                     :exec (or (and (= a d) (= b cb))
                               (and (= a c) (= b db)))))
          (mv (lit-negate a) nil lit1 lit2))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond b a c d cb db)
                     :exec (or (and (= b d) (= a cb))
                               (and (= b c) (= a db)))))
          (mv (lit-negate b) nil lit1 lit2)))
      (mv nil nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step3-cond)))
    :eval-hints (;; ("goal" :in-theory (e/d (eval-and-of-lits
                 ;;                           equal-of-mk-lit-neg)
                 ;;                         (id-eval)))
                 (and stable-under-simplificationp
                      '(:expand (;; (lit-eval lit1 aignet-invals aignet-regvals aignet)
                                 ;; (lit-eval lit2 aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit1) aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit2) aignet-invals aignet-regvals aignet)
                                 (:free (a b c d cb db)
                                  (aignet-gate-simp-l2-step3-cond a b c d cb
                                                                  db)))
                        :in-theory (e/d (lit-eval-open
                                         eval-and-of-lits
                                         equal-of-mk-lit-neg)
                                        (id-eval))))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor
                                         b-and
                                         b-not)
                                        (id-eval))))))

  (def-gate-simp aignet-gate-simp-level2
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step1 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2))
         ((when (not both)) (mv nil nil lit1 lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step2 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step3 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2)))
      (mv nil nil lit1 lit2))
    :extra-args (both)
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (implies both
                         (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (implies both
                    (int= (id->type (lit-id lit2) aignet) (gate-type)))))

  (defund aignet-gate-simp-level3-cond1.1 (ab c d)
    (or (= ab c) (= ab d)))

  (defund aignet-gate-simp-level3-cond1 (ab c d lit2 negp2 both)
    (or (= ab lit2)                                     ;; substitution1
        (and both (not negp2)
             (aignet-gate-simp-level3-cond1.1 ab c d))))

  (defund aignet-gate-simp-level3-cond2 (a b cd)
    (or (= cd b) (= cd a)))

  (defthm lit-eval-of-mk-lit-opposite
    (implies (equal b (b-not (lit-neg lit)))
             (equal (lit-eval (mk-lit (lit-id lit) b) aignet-invals aignet-regvals aignet)
                    (b-not (lit-eval lit aignet-invals aignet-regvals aignet))))
    :hints(("Goal" :in-theory (enable b-not b-xor lit-eval))))

  (def-gate-simp aignet-gate-simp-level3
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         ((mv c d) (if both
                       (let ((id2 (lit-id lit2)))
                         (mv (gate-id->fanin0 id2 aignet)
                             (gate-id->fanin1 id2 aignet)))
                     (mv nil nil)))
         (negp1 (int= (lit-neg lit1) 1))
         (negp2 (int= (lit-neg lit2) 1))

         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 b c d lit2 negp2 both)
                          :exec
                          (or (= b lit2)                                      ;; substitution1
                              (and both (not negp2) (or (= b c) (= b d))))))) ;; substitution2
          (mv nil t (lit-negate a) lit2))
         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 a c d lit2 negp2 both)
                          :exec
                          (or (= a lit2)                                      ;; substitution1
                              (and both (not negp2) (or (= a c) (= a d))))))) ;; substitution2
          (mv nil t (lit-negate b) lit2))
         ((when (and both (int= 1 (b-and (lit-neg lit2) (b-not (lit-neg lit1))))
                     (mbe :logic (aignet-gate-simp-level3-cond2 a b c)
                          :exec (or (= c b) (= c a))))) ;; substitution2
          (mv nil t (lit-negate d) lit1))
         ((when  (and both (int= 1 (b-and (lit-neg lit2) (b-not (lit-neg lit1))))
                      (mbe :logic (aignet-gate-simp-level3-cond2 a b d)
                           :exec (or (= d b) (= d a))))) ;; substitution2
          (mv nil t (lit-negate c) lit1)))
      (mv nil nil lit1 lit2))
    :extra-args (both)
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (implies both
                         (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (implies both
                    (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-level3-cond1
                                             aignet-gate-simp-level3-cond1.1
                                             aignet-gate-simp-level3-cond2)))
    :eval-hints (;; ("goal" :in-theory (e/d (eval-and-of-lits
                 ;;                          equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((lit-eval lit1 aignet-invals aignet-regvals aignet)
                                 (lit-eval lit2 aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit1) aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit2) aignet-invals aignet-regvals aignet))
                        :in-theory (enable aignet-gate-simp-level3-cond1
                                           aignet-gate-simp-level3-cond1.1
                                           aignet-gate-simp-level3-cond2
                                           equal-of-mk-lit-neg
                                           eval-and-open)))

                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not)
                                        (id-eval))))))

  (defund aignet-gate-simp-level4-cond (ab c d)
    (or (= ab c) (= ab d)))

  (def-gate-simp aignet-gate-simp-level4
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((when (or (int= (lit-neg lit1) 1)
                    (int= (lit-neg lit2) 1)))
          (mv nil nil lit1 lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         ;; For each equality, we could either reduce the left or right gate.
         ;; Maybe experiment with this.  Atm. we'll prefer to reduce the
         ;; higher-numbered gate, lit1.
         ((when (mbe :logic (aignet-gate-simp-level4-cond a c d)
                     :exec (or (= a c) (= a d))))
          (mv nil t b lit2))
         ((when (mbe :logic (aignet-gate-simp-level4-cond b c d)
                     :exec (or (= b c) (= b d))))
          (mv nil t a lit2)))
      (mv nil nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-level4-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-open
                                          equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((lit-eval lit1 aignet-invals aignet-regvals aignet)
                                 (lit-eval lit2 aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit1) aignet-invals aignet-regvals aignet)
                                 (id-eval (lit-id lit2) aignet-invals aignet-regvals aignet))
                        :in-theory (enable aignet-gate-simp-level4-cond
                                           eval-and-open)))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not)
                                        (id-eval))))))

  (def-gate-simp aignet-gate-simp-pass
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (level (lnfix level))
         ((when (< level 1))
          (mv nil nil lit1 lit2))

         ((mv level1-result & & &) (aignet-gate-simp-level1 lit1 lit2 aignet))
         ((when level1-result)
          (mv level1-result nil lit1 lit2))

         ((mv lit1 lit2 both neither)
          (aignet-gate-simp-order lit1 lit2 aignet))

         ((when (or (< level 2) neither))
          (mv nil nil lit1 lit2))

         ;; O2.
         ;; Only one direction possible since lit2 < lit1.
         ((mv level2-result & & &) (aignet-gate-simp-level2 lit1 lit2 both aignet))
         ((when level2-result)
          (mv level2-result nil lit1 lit2))

         ((when (< level 3))
          (mv nil nil lit1 lit2))


         ;; O3.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level3 lit1 lit2 both aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2))

         ((when (or (< level 4) (not both)))
          (mv nil nil lit1 lit2))

         ;; O4.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level4 lit1 lit2 aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2)))

      (mv nil nil lit1 lit2))

    :extra-args (level)
    :guard (natp level)
    :fanin-hints (("goal" :cases ((mv-nth 2 (aignet-gate-simp-order lit1 lit2 aignet)))))
    :measure-hints (("goal" :use ((:instance
                                   two-id-measure-of-aignet-gate-simp-order))
                     :in-theory (disable
                                 two-id-measure-of-aignet-gate-simp-order))))

  (local
   (set-default-hints
    '((and (equal id (acl2::parse-clause-id "goal"))
           '(:induct (aignet-gate-simp lit1 lit2 level aignet)
             :do-not-induct t
             :in-theory (disable (:definition aignet-gate-simp))
             :expand ((:free (lit2 aignet) (aignet-gate-simp lit1 lit2 level aignet))
                      (:free (lit1 aignet) (aignet-gate-simp lit1 lit2 level aignet))))))))

  (local (in-theory (disable eval-and-of-lits)))

  (def-gate-simp aignet-gate-simp
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((mv exists reduced nlit1 nlit2)
          (aignet-gate-simp-pass lit1 lit2 level aignet))
         ((when exists)
          (mv exists nil nlit1 nlit2))
         ((unless reduced)
          (mv nil nil nlit1 nlit2))
         ;; check measure
         ((unless (mbt (o< (two-id-measure (lit-id nlit1) (lit-id nlit2))
                           (two-id-measure (lit-id lit1) (lit-id lit2)))))
          (mv nil nil nlit1 nlit2)))
      (aignet-gate-simp nlit1 nlit2 level aignet))

    :extra-args (level)
    :guard (natp level)
    :xargs (:measure (two-id-measure (lit-id lit1) (lit-id lit2))
            :hints (("goal" :in-theory (enable two-id-measure)))
            :guard-hints (("goal" :no-thanks t)))
    :skip-measure t))

(defsection aignet-addr-combine
  ;; Combining two integers into one (generally fixnum) key for hashing:
  ;; This is the same as hl-addr-combine (in books/system/hl-addr-combine.lisp)
  ;; but we don't need to prove anything about it here beyond verifying
  ;; guards (which are simpler here because we don't need the MBE).

  #!ACL2
  (local (defthm +-of-logcons-with-cin
           (implies (bitp cin)
                    (equal (+ cin
                              (logcons b1 r1)
                              (logcons b2 r2))
                           (logcons (b-xor cin (b-xor b1 b2))
                                    (+ (b-ior (b-and cin b1)
                                              (b-ior (b-and cin b2)
                                                     (b-and b1 b2)))
                                       (ifix r1)
                                       (ifix r2)))))
           :hints(("Goal" :in-theory (enable logcons b-ior b-and b-xor b-not)))))
  (local
   (defthm logior-to-plus
     (implies (and (natp a)
                   (integerp b)
                   (natp n)
                   (< a (ash 1 n)))
              (equal (logior a (ash b n))
                     (+ a (ash b n))))
     :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions)
; (acl2::ash-1-removal)
                                     )
             :induct (logbitp n a)
             :expand ((:free (b) (ash b n))
                      (:free (b) (logior a b))))
            (and stable-under-simplificationp
                 '(:use ((:instance acl2::+-of-logcons-with-cin
                          (acl2::b1 (acl2::logcar a))
                          (acl2::r1 (acl2::logcdr a))
                          (acl2::b2 0)
                          (acl2::r2 (ash b (+ -1 n)))
                          (acl2::cin 0))))))))

  (local (defthm floor-of-1
           (implies (natp n)
                    (equal (floor n 1) n))
           :hints(("Goal" :in-theory (enable floor)))))

  (defund aignet-addr-combine (a b)
    (declare (type (integer 0 *) a b)
             (xargs ;; :guard (and (natp a) (natp b))
                    :verify-guards nil))
    (if (and (< a 1073741824)
             (< b 1073741824))
        ;; Optimized version of the small case
        (the (signed-byte 61)
          (- (the (signed-byte 61)
               (logior (the (signed-byte 61)
                         (ash (the (signed-byte 31) a) 30))
                       (the (signed-byte 31) b)))))
      ;; Large case.
      (- (+ (let* ((a+b   (+ a b))
                   (a+b+1 (+ 1 a+b)))
              (if (= (logand a+b 1) 0)
                  (* (ash a+b -1) a+b+1)
                (* a+b (ash a+b+1 -1))))
            b)
         576460752840294399)))

  (local (in-theory (enable aignet-addr-combine)))

  (verify-guards aignet-addr-combine
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ash))))
    :otf-flg t))

(defsection strash
  (defstobj strash
    (strashtab :type (hash-table eql))
    :inline t)

  ;; returns (mv exists key id).
  ;; exists implies that id is a gate with the two specified fanins.
  (definlined strash-lookup (lit1 lit2 strash aignet)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (litp lit1) (fanin-litp lit1 aignet)
                                (litp lit2) (fanin-litp lit2 aignet))))
    (b* ((key (aignet-addr-combine (lit-val lit1) (lit-val lit2)))
         (id (strashtab-get key strash))
         ((unless (and (natp id)
                       (id-existsp id aignet)
                       (int= (id->type id aignet) (gate-type))
                       (int= (gate-id->fanin0 id aignet) lit1)
                       (int= (gate-id->fanin1 id aignet) lit2)))
          (mv nil key 0)))
      (mv t key id)))

  (local (in-theory (enable strash-lookup)))

  (defthm strash-lookup-correct
    (b* (((mv found & id) (strash-lookup lit1 lit2 strash aignet)))
      (implies found
               (and (aignet-idp id aignet)
                    (aignet-litp (mk-lit id bit) aignet)
                    (b* (((cons node tail) (lookup-id id aignet)))
                      (and (equal (stype node) (gate-stype))
                           (equal (aignet-lit-fix (gate-node->fanin0 node) tail) lit1)
                           (equal (aignet-lit-fix (gate-node->fanin1 node)
                                                  tail) lit2))))))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm strash-lookup-id-type
    (natp (mv-nth 2 (strash-lookup lit1 lit2 strash aignet)))
    :rule-classes (:rewrite :type-prescription))

  (defthm strash-lookup-key-type
    (acl2-numberp (mv-nth 1 (strash-lookup lit1 lit2 strash aignet)))
    :rule-classes :type-prescription))

(defsection gatesimp
  (local (in-theory (disable len-update-nth)))
  (local (in-theory (enable* acl2::ihsext-recursive-redefs
                             acl2::ihsext-bounds-thms
                             nfix natp)))

  (definlined gatesimp-level (gatesimp)
    (declare (Xargs :guard (natp gatesimp)))
    (ash (lnfix gatesimp) -1))

  (defthm natp-gatesimp-level
    (natp (gatesimp-level gatesimp))
    :hints(("Goal" :in-theory (enable gatesimp-level)))
    :rule-classes :type-prescription)

  (definlined gatesimp-hashp (gatesimp)
    (declare (Xargs :guard (natp gatesimp)))
    (logbitp 0 gatesimp))

  (definlined mk-gatesimp (level hashp)
    (declare (xargs :guard (natp level)))
    (logior (ash (lnfix level) 1) (if hashp 1 0)))

  (defthm gatesimp-level-of-mk-gatesimp
    (equal (gatesimp-level (mk-gatesimp level hashp))
           (nfix level))
    :hints(("Goal" :in-theory (enable gatesimp-level mk-gatesimp))))

  (defthm gatesimp-hashp-of-mk-gatesimp
    (equal (gatesimp-hashp (mk-gatesimp level hashp))
           (if hashp
               t
             nil))
    :hints(("Goal" :in-theory (enable gatesimp-hashp mk-gatesimp))))

  (defthm natp-mk-gatesimp
    (natp (mk-gatesimp level hashp))
    :hints(("Goal" :in-theory (enable mk-gatesimp)))
    :rule-classes :type-prescription))

(define aignet-hash-and ((lit1 litp)
                         (lit2 litp)
                         (gatesimp natp)
                         strash
                         aignet)
  (declare (type (integer 0 *) lit1)
           (type (integer 0 *) lit2)
           (type (integer 0 *) gatesimp)
           (xargs :guard (and (fanin-litp lit1 aignet)
                              (fanin-litp lit2 aignet))))
  (b* ((lit1 (lit-fix lit1))
       (lit2 (lit-fix lit2))
       (gatesimp (lnfix gatesimp))
       ((mv existing & lit1 lit2)
        (aignet-gate-simp lit1 lit2 (gatesimp-level gatesimp) aignet))
       ((when existing)
        (mv existing strash aignet))
       ((when (not (gatesimp-hashp gatesimp)))
        (b* ((lit (mk-lit (num-nodes aignet) 0))
             (aignet (aignet-add-gate lit1 lit2 aignet)))
          (mv lit strash aignet)))
       ((mv found key id) (strash-lookup lit1 lit2 strash aignet))
       ((when found)
        (mv (mk-lit id 0) strash aignet))
       (lit (mk-lit (num-nodes aignet) 0))
       (aignet (aignet-add-gate lit1 lit2 aignet))
       (strash (strashtab-put key (lit-id lit) strash)))
    (mv lit strash aignet))

  ///

  (defthm litp-of-aignet-hash-and
    (litp (mv-nth 0 (aignet-hash-and lit1 lit2 gatesimp strash aignet))))

  (defmvtypes aignet-hash-and (natp nil nil))

  (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 1)
  (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 2)
  (defcong nat-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 3)

  (def-aignet-preservation-thms aignet-hash-and)

  (defthm aignet-idp-of-new-node
    (aignet-idp (+ 1 (node-count aignet))
                (cons new-node aignet))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-litp-of-new-node
    (implies (not (equal (ctype (stype new-node)) (out-ctype)))
             (aignet-litp (mk-lit (+ 1 (node-count aignet)) neg)
                          (cons new-node aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-litp-of-aignet-hash-and
    (b* (((mv lit & aignet)
          (aignet-hash-and lit1 lit2 gatesimp strash aignet1)))
      (implies (and (aignet-litp lit1 aignet1)
                    (aignet-litp lit2 aignet1))
               (aignet-litp lit aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-litp)))))

  (defthm id-eval-of-strash-lookup
    (b* (((mv ok & id)
          (strash-lookup lit1 lit2 strash aignet)))
      (implies ok
               (equal (id-eval id aignet-invals aignet-regvals aignet)
                      (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals aignet))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits id-eval))))


  (defthm lit-eval-of-aignet-hash-and
    (b* (((mv res & newaignet)
          (aignet-hash-and lit1 lit2 gatesimp strash aignet)))
      (equal (lit-eval res aignet-invals aignet-regvals newaignet)
             (b-and (lit-eval lit1 aignet-invals aignet-regvals aignet)
                    (lit-eval lit2 aignet-invals aignet-regvals aignet))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d
                               (eval-and-of-lits
                                lit-eval-of-aignet-lit-fix
                                lit-eval)
                               (eval-of-aignet-gate-simp))
                   :use ((:instance eval-of-aignet-gate-simp
                          (level (gatesimp-level (nfix gatesimp)))
                          (lit1 (lit-fix lit1))
                          (lit2 (lit-fix lit2))))))))


  (defthm stype-counts-preserved-of-aignet-hash-and
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype
                                 (mv-nth 2 (aignet-hash-and
                                            lit1 lit2 gatesimp strash aignet)))
                    (stype-count stype aignet)))))


(defsection aignet-construction
  :parents (aignet)
  :short "How to construct an AIGNET network."
  :autodoc nil
  :long "
<p>An AIGNET network is constructed by adding nodes in topological
order: that is, an AND gate cannot be added until its two fanins are created,
and a combinational output cannot be added until its fanin exists.
Additionally, a register input cannot be added until its corresponding register
output exists.</p>

<p>First, because an AIGNET network is represented in a stobj, you must either
work on the \"live\" @('AIGNET') stobj or else create a local one using
@(see with-local-stobj).</p>

<p>Usually when constructing an AIG network one wants to structurally hash the
AND nodes, so as to avoid creating duplicate nodes with identical structure.
To do this, you additionally need a @('STRASH') stobj, which again may either
be the live one or one created locally.</p>

<p>To initialize a new network or clear an existing one, use:
@({ (aignet-clear aignet) })
or, to allocate a certain amount of space in order to avoid resizing arrays,
@({ (aignet-init output-cap reg-cap input-cap node-cap aignet). })</p>

<p>To initialize a strash object or clear an existing one, use:
@({ (strashtab-clear strash) })
or to allocate a certain amount of space to avoid resizing the hash table,
@({ (strashtab-init node-cap nil nil strash). })</p>

<h1>Aigaignet-construction functions</h1>
<p>@('(aignet-add-in aignet)') adds a new primary input node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-reg aignet)') adds a new register output node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-gate lit1 lit2 aignet)') adds to the network a new AND node
conjoining <tt>lit1</tt> and <tt>lit2</tt>, and returns <tt>(mv lit aignet)</tt>,
where <tt>lit</tt> is the non-negated literal of the new node.  <tt>lit1</tt>
and <tt>lit2</tt> must be literals of the network, satisfying
@('aignet-litp') (which is true of any literal returned by a node construction
function, or its negation).  Note: this function does not do structural
hashing -- for that, see below.</p>

<p>@('(aignet-add-out lit aignet)') adds to the network a new primary output with
fanin <tt>lit</tt>, and returns <tt>aignet</tt>.  (It does not return a literal
because a combinational output node is not allowed to be the fanin to another
node.)  <tt>lit</tt> must satisfy @('aignet-litp').</p>

<p>@('(aignet-add-regin lit ro aignet)') adds to the network a new register input
with fanin <tt>lit</tt>, and connects it to a register output node whose ID is
<tt>ro</tt>.  It returns <tt>aignet</tt>.  <tt>lit</tt> must satisfy @('aignet-litp')
and <tt>ro</tt> must be the ID of a register output node that is not yet
connected to a register input.</p>

<p>The following functions:
@({
    (aignet-hash-and f1 f2 gatesimp strash aignet)
    (aignet-hash-or  f1 f2 gatesimp strash aignet)
    (aignet-hash-xor f1 f2 gatesimp strash aignet)
    (aignet-hash-mux c tb fb gatesimp strash aignet) })

add nodes implementing the respective functions of input literals <tt>f1</tt>
and <tt>f2</tt> (for and/or/xor) and <tt>c</tt>, <tt>tb</tt>, and <tt>fb</tt>
for mux (signifying condition, true-branch, and false-branch), possibly with
structural hashing and lightweight simplification.  All return
<code>(mv lit strash aignet).</code>
Gatesimp is an object that specifies both whether to
structurally hash the nodes and what level of effort to use in Boolean
simplification, between 0 and 4.  The levels of simplification correspond to
the paper:

<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>

available <a
href=\"http://megaknowledge.info/cadathlon/2007/refs/p5-verification.pdf\">here</a>.
These simplifications look at most one level deep at the fanins of each AND,
that is, examining at most four fanin nodes.  Usually at least level 1 is
desirable; level 1 deals with ANDs of constants and identical and negated
nodes.  Practically, we think for most applications building the AIGs is not a
performance bottleneck and level 3 or 4 can be used with some potential benefit
and no noticeable slowdown.</p>

<p>To construct a gatesimp object, use @('(mk-gatesimp level hashp)'), where
level is from 0-4 as above and hashp is Boolean and causes structural hashing
to be done if non-<tt>NIL</tt>.</p>")




(define aignet-hash-or ((f0 litp)
                        (f1 litp)
                        (gatesimp natp)
                        strash
                        aignet)
  :inline t
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  (b* (((mv lit strash aignet)
        (aignet-hash-and (lit-negate f0) (lit-negate f1) gatesimp strash aignet)))
    (mv (lit-negate lit) strash aignet))

  ///

  (def-aignet-preservation-thms aignet-hash-or)

  (defthm litp-aignet-hash-or
    (litp (mv-nth 0 (aignet-hash-or lit1 lit2 gatesimp strash aignet))))

  (defcong lit-equiv equal (aignet-hash-or f0 f1 gatesimp strash aignet) 1)
  (defcong lit-equiv equal (aignet-hash-or f0 f1 gatesimp strash aignet) 2)
  (defcong nat-equiv equal (aignet-hash-or f0 f1 gatesimp strash aignet) 3)

  (defthm aignet-litp-aignet-hash-or
    (implies (and (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet))
             (b* (((mv lit & aignet)
                   (aignet-hash-or lit1 lit2 gatesimp strash aignet)))
               (aignet-litp lit aignet))))

  (defthm lit-eval-of-aignet-hash-or
    (b* (((mv lit & aignet1)
          (aignet-hash-or lit1 lit2 gatesimp strash aignet)))
      (equal (lit-eval lit aignet-invals aignet-regvals aignet1)
             (b-ior (lit-eval lit1 aignet-invals aignet-regvals aignet)
                    (lit-eval lit2 aignet-invals aignet-regvals aignet))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits
                                      b-ior b-and
                                      b-not))))

  (defthm stype-counts-preserved-of-aignet-hash-or
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 2 (aignet-hash-or
                                                  f0 f1 gatesimp strash
                                                  aignet)))
                    (stype-count stype aignet)))))

(define aignet-hash-mux ((c litp)
                         (tb litp)
                         (fb litp)
                         (gatesimp natp)
                         strash
                         aignet)
  :inline t
  :guard (and (fanin-litp c aignet)
              (fanin-litp tb aignet)
              (fanin-litp fb aignet))
  (b* ((c (mbe :logic (non-exec (aignet-lit-fix c aignet))
               :exec c))
       (tb (mbe :logic (non-exec (aignet-lit-fix tb aignet))
                :exec tb))
       (fb (mbe :logic (non-exec (aignet-lit-fix fb aignet))
                :exec fb))
       ((mv c-tb strash aignet)
        (aignet-hash-and c tb gatesimp strash aignet))
       ((mv nc-fb strash aignet)
        (aignet-hash-and (lit-negate c) fb gatesimp strash aignet)))
    (aignet-hash-or c-tb nc-fb gatesimp strash aignet))

  ///

  (def-aignet-preservation-thms aignet-hash-mux)

  (defthm litp-aignet-hash-mux
    (litp (mv-nth 0 (aignet-hash-mux c tb fb gatesimp strash aignet))))

  (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 1)
  (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 2)
  (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 3)
  (defcong nat-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 4)

  (defthm aignet-litp-aignet-hash-mux
    (implies (and (aignet-litp c aignet)
                  (aignet-litp tb aignet)
                  (aignet-litp fb aignet))
             (b* (((mv lit & aignet)
                   (aignet-hash-mux c tb fb gatesimp strash aignet)))
               (aignet-litp lit aignet))))

  (defthm lit-eval-of-aignet-hash-mux
    (b* (((mv lit & aignet1)
          (aignet-hash-mux c tb fb gatesimp strash aignet)))
      (equal (lit-eval lit aignet-invals aignet-regvals aignet1)
             (b-ior (b-and
                     (lit-eval c aignet-invals aignet-regvals aignet)
                     (lit-eval tb aignet-invals aignet-regvals aignet))
                    (b-and
                     (b-not
                      (lit-eval c aignet-invals aignet-regvals aignet))
                     (lit-eval fb aignet-invals aignet-regvals aignet)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable lit-eval-of-aignet-lit-fix)))))

  (defthm stype-counts-preserved-of-aignet-hash-mux
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 2 (aignet-hash-mux
                                                  c tb fb gatesimp strash
                                                  aignet)))
                    (stype-count stype aignet)))))

(define aignet-hash-xor ((f0 litp)
                         (f1 litp)
                         (gatesimp natp)
                         strash
                         aignet)
  :inline t
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  (aignet-hash-mux f0 (lit-negate f1) f1 gatesimp strash aignet)

  ///

  (def-aignet-preservation-thms aignet-hash-xor)

  (defthm litp-aignet-hash-xor
    (litp (mv-nth 0 (aignet-hash-xor lit1 lit2 gatesimp strash aignet))))

  (defcong lit-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 1)
  (defcong lit-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 2)
  (defcong nat-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 3)

  (defthm aignet-litp-aignet-hash-xor
    (implies (and (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet))
             (b* (((mv lit & aignet)
                   (aignet-hash-xor lit1 lit2 gatesimp strash aignet)))
               (aignet-litp lit aignet)))
    :hints(("Goal" :in-theory (disable aignet-hash-mux))))

  (defthm lit-eval-of-aignet-hash-xor
    (b* (((mv lit & aignet1)
          (aignet-hash-xor lit1 lit2 gatesimp strash aignet)))
      (equal (lit-eval lit aignet-invals aignet-regvals aignet1)
             (b-xor (lit-eval lit1 aignet-invals aignet-regvals aignet)
                    (lit-eval lit2 aignet-invals aignet-regvals aignet))))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable b-xor b-and b-ior)))))

  (defthm stype-counts-preserved-of-aignet-hash-xor
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 2 (aignet-hash-xor
                                                  f0 f1 gatesimp strash
                                                  aignet)))
                    (stype-count stype aignet)))))
