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
(include-book "centaur/fty/bitstruct" :dir :system)
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
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

(local (in-theory (disable BITOPS::commutativity-of-b-xor
                           BITOPS::BXOR-TO-BNOT
                           BITOPS::BXOR-TO-ID
                           BITOPS::B-AND-EQUAL-1-IN-HYP)))

(local (acl2::use-trivial-ancestors-check))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable unsigned-byte-p)))

(local (defthm unsigned-byte-p-of-lit->var
         (implies (and (unsigned-byte-p (+ 1 n) lit)
                       (natp n))
                  (unsigned-byte-p n (lit->var lit)))
         :hints(("Goal" :in-theory (enable lit->var)))))

(local (defthmd unsigned-byte-p-of-lit-when-lit->var
         (implies (and (unsigned-byte-p (+ -1 n) (lit->var lit))
                       (litp lit)
                       (posp n))
                  (unsigned-byte-p n lit))
         :hints(("Goal" :in-theory (enable lit->var)))
         :rule-classes ((:rewrite :backchain-limit-lst (3 nil nil)))))

(local (defthm unsigned-byte-p-of-lit->var-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (< (node-count aignet) #x1fffffff))
                  (unsigned-byte-p 29 (lit->var lit)))
         :hints(("Goal" :in-theory (enable aignet-litp unsigned-byte-p)))))

(local (defthm unsigned-byte-p-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (litp lit)
                       (< (node-count aignet) #x1fffffff))
                  (unsigned-byte-p 30 lit))
         :hints(("Goal" :in-theory (enable unsigned-byte-p-of-lit-when-lit->var)))))

(local (defthm unsigned-byte-p-32-when-aignet-litp
         (implies (and (aignet-litp lit aignet)
                       (litp lit)
                       (< (node-count aignet) #x1fffffff))
                  (unsigned-byte-p 32 lit))
         :hints(("Goal" :use unsigned-byte-p-when-aignet-litp
                 :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

(local (defthmd unsigned-byte-p-when-bit
         (implies (and (bitp x)
                       (posp n))
                  (unsigned-byte-p n x))
         :hints(("Goal" :in-theory (enable bitp)))))
                  

(local (defthm unsigned-byte-p-of-lit-negate
         (implies (and (unsigned-byte-p n x)
                       (posp n))
                  (unsigned-byte-p n (lit-negate x)))
         :hints(("Goal" :in-theory (enable lit-negate make-lit lit->var
                                           unsigned-byte-p-when-bit)))))

(local (defthm unsigned-byte-p-of-fanin
         (implies (< (node-count aignet) #x1fffffff)
                  (unsigned-byte-p 30 (fanin type (lookup-id id aignet))))
         :hints(("Goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                               (lit (fanin type (lookup-id id aignet)))))
                 :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

(local (defthm unsigned-byte-p-32-of-fanin
         (implies (< (node-count aignet) #x1fffffff)
                  (unsigned-byte-p 32 (fanin type (lookup-id id aignet))))
         :hints(("Goal" :use ((:instance unsigned-byte-p-of-fanin))
                 :in-theory (disable unsigned-byte-p-of-fanin)))))

(defmacro =30 (a b)
  `(eql (the (unsigned-byte 30) ,a)
        (the (unsigned-byte 30) ,b)))

(defmacro =2 (a b)
  `(eql (the (unsigned-byte 2) ,a)
        (the (unsigned-byte 2) ,b)))

(defmacro =b (a b)
  `(eql (the bit ,a)
        (the bit ,b)))

(defmacro <29 (a b)
  `(< (the (unsigned-byte 29) ,a)
      (the (unsigned-byte 29) ,b)))
                  



(defsection simplify-gate

;  (local (include-book "bit-lemmas"))

  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::bfix-when-not-bitp
                             id-eval
                             ;; equal-of-to-lit-backchain
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

    ;; (defthm two-id-measure-of-gate
    ;;   (implies (and (equal (id->type id1 aignet) (gate-type))
    ;;                 (aignet-idp id1 aignet))
    ;;            (b* (((cons node rest) (lookup-id id1 aignet))
    ;;                 (ch1 (aignet-lit-fix (gate-node->fanin0 node) rest))
    ;;                 (ch2 (aignet-lit-fix (gate-node->fanin1 node) rest)))
    ;;              (and (o< (two-id-measure id2 (lit-id ch1))
    ;;                       (two-id-measure id1 id2))
    ;;                   (o< (two-id-measure id2 (lit-id ch2))
    ;;                       (two-id-measure id1 id2))
    ;;                   (o< (two-id-measure id2 (lit-id ch1))
    ;;                       (two-id-measure id2 id1))
    ;;                   (o< (two-id-measure id2 (lit-id ch2))
    ;;                       (two-id-measure id2 id1))))))
    
    (defthm two-id-measure-of-fanin
      (implies (and (equal (id->type id1 aignet) (gate-type))
                    (aignet-idp id1 aignet))
               (b* ((ch1 (fanin ftype (lookup-id id1 aignet))))
                 (and (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id2 id1))))))

    ;; (defthm two-id-measure-of-fanin
    ;;   (implies (and (aignet-nodes-ok aignet)
    ;;                 (equal (id->type id1 aignet) (out-type))
    ;;                 (aignet-idp id1 aignet))
    ;;            (b* ((ch1 (fanin ftype (lookup-id id1 aignet))))
    ;;              (and (o< (two-id-measure id2 (lit-id ch1))
    ;;                       (two-id-measure id1 id2))
    ;;                   (o< (two-id-measure id2 (lit-id ch1))
    ;;                       (two-id-measure id2 id1))))))
    )

  (define aignet-gate-simp-order ((lit1 litp :type (unsigned-byte 30))
                                  (lit2 litp :type (unsigned-byte 30))
                                  aignet)
    :split-types t
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet))
    :returns (mv (lit1 litp)
                 (lit2 litp)
                 both neither)
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit->var^ lit1))
         (id2 (lit->var^ lit2))
         (gatep1 (=2 (id->type id1 aignet) (gate-type)))
         (gatep2 (=2 (id->type id2 aignet) (gate-type)))
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
          (if (<29 id2 id1)
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
                       (skip-precedes 'nil)
                       (aignet-litp-hints 'nil)
                       ;; (lit-cong1-hints 'nil)
                       ;; (lit-cong2-hints 'nil)
                       ;; (list-cong-hints 'nil)
; (nth-cong-hints 'nil)
                       (xargs 'nil))
   `(define ,name ((lit1 litp :type (unsigned-byte 30))
                   (lit2 litp :type (unsigned-byte 30))
                   ,@extra-args
                   aignet)
      (declare (xargs . ,xargs))
      :split-types t
      :guard (and (fanin-litp lit1 aignet)
                  (fanin-litp lit2 aignet)
                  ,guard)
      :guard-hints ,guard-hints
      :returns (mv (extra acl2::maybe-natp :rule-classes :type-prescription)
                   (flg)
                   (nlit1 litp :rule-classes :type-prescription)
                   (nlit2 litp :rule-classes :type-prescription))
      ,body
      ///

      ;; (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 1
      ;;   :hints ,lit-cong1-hints)
      ;; (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 2
      ;;   :hints ,lit-cong2-hints)
      ;; (defcong list-equiv equal (,name lit1 lit2 ,@extra-args aignet)
      ;;   ,(+ 3 (len extra-args))
      ;;   :hints ,list-cong-hints)

      ,@(and
         (not skip-precedes)
         `((defret ,(mksym name "FANIN-PRECEDES-GATE-OF-" (symbol-name name))
             (implies (and (< (lit-id lit1) gate)
                           (< (lit-id lit2) gate)
                           ;; (aignet-litp lit1 aignet)
                           ;; (aignet-litp lit2 aignet)
                           (natp gate)
                           . ,reqs)
                      (and (implies extra
                                    (< (lit-id extra) gate))
                           (< (lit-id nlit1) gate)
                           (< (lit-id nlit2) gate)))
             :hints ,fanin-hints
             :rule-classes (:rewrite))))

      ,@(and
         (not skip-measure)
         `((defret ,(mksym name "TWO-ID-MEASURE-OF-" (symbol-name name))
             (implies (and ;; (aignet-litp lit1 aignet)
                           ;; (aignet-litp lit2 aignet)
                           . ,reqs)
                      (implies flg
                               (o< (two-id-measure (lit-id nlit1)
                                                   (lit-id nlit2))
                                   (two-id-measure (lit-id lit1)
                                                   (lit-id lit2)))))
             :hints ,measure-hints)))

      (defret ,(mksym name "AIGNET-LITP-OF-" (symbol-name name))
        (implies (and (aignet-litp lit1 aignet)
                      (aignet-litp lit2 aignet)
                      . ,reqs)
                 (and (implies extra
                               (aignet-litp extra aignet))
                      (aignet-litp nlit1 aignet)
                      (aignet-litp nlit2 aignet)))
        :hints ,aignet-litp-hints)


      (defret ,(mksym name "EVAL-OF-" (symbol-name name))
        (implies (and ;; (aignet-litp lit1 aignet)
                  ;; (aignet-litp lit2 aignet)
                  . ,reqs)
                 (and (implies extra
                               (equal (lit-eval extra aignet-invals aignet-regvals aignet)
                                      (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals
                                                        aignet)))
                      (equal (eval-and-of-lits nlit1 nlit2 aignet-invals aignet-regvals aignet)
                             (eval-and-of-lits lit1 lit2 aignet-invals aignet-regvals aignet))))
        :hints ,eval-hints)

      ;; (defret ,(mksym name "LITP-OF-" (symbol-name name))
      ;;   (and (implies extra
      ;;                 (litp extra))
      ;;        (litp nlit1)
      ;;        (litp nlit2)))
      ))


  (local (in-theory (disable len)))

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

  (defthm b-and-of-xor-not-free
    (implies (equal c (b-not a))
             (equal (b-and (b-xor c b)
                           (b-xor a b))
                    0))
    :hints(("Goal" :in-theory (enable b-and b-xor b-not))))

  (def-gate-simp aignet-gate-simp-level1
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((when (=2 (id->type (lit->var^ lit1) aignet) (const-type)))
          (mv (if (=b (lit->neg^ lit1) 1)
                  lit2    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (=2 (id->type (lit->var^ lit2) aignet) (const-type)))
          (mv (if (=b (lit->neg^ lit2) 1)
                  lit1    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (=30 lit1 lit2))
          (mv lit1 nil lit1 lit2))       ;; idempotence
         ((when (=30 lit1 (lit-negate^ lit2)))
          (mv 0 nil lit1 lit2)))         ;; contradiction
      (mv nil nil lit1 lit2))
    :eval-hints (("Goal" :in-theory (e/d* (eval-and-of-lits
                                           id-eval lit-eval
                                           satlink::equal-of-make-lit
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
         (id1 (lit->var^ lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (lit2b (lit-negate^ lit2))
         (res (or (and (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2b)
                            :exec (or (=30 a lit2b)
                                      (=30 b lit2b)))
                       (if (=b (lit->neg^ lit1) 1)
                           lit2 ;; subsumption1
                         0))    ;; contradiction1
                  (and (eql (the bit (lit->neg^ lit1)) 0)
                       (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2)
                            :exec (or (=30 a lit2)
                                      (=30 b lit2)))
                       lit1))))  ;; idempotence1
      (mv res nil lit1 lit2))
    :guard (int= (id->type (lit-id lit1) aignet) (gate-type))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step1-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-of-lits lit-eval
                                                           satlink::equal-of-make-lit)))
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
           :hints(("Goal" :in-theory (enable satlink::equal-of-make-lit)))))

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
         (id1 (lit->var^ lit1))
         (id2 (lit->var^ lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (negp1 (=b (lit->neg^ lit1) 1))
         (negp2 (=b (lit->neg^ lit2) 1))
         (cb (lit-negate^ c))
         (db (lit-negate^ d))
         (res (and (=b 0 (b-and (lit->neg^ lit1) (lit->neg^ lit2)))
                   (mbe :logic (aignet-gate-simp-l2-step2-cond a b cb db)
                        :exec (or (=30 a cb)
                                  (=30 a db)
                                  (=30 b cb)
                                  (=30 b db)))
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
         ((unless (=b 1 (b-and (lit->neg^ lit1)
                               (lit->neg^ lit2))))
          (mv nil nil lit1 lit2))
         (id1 (lit->var^ lit1))
         (id2 (lit->var^ lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (cb (lit-negate^ c))
         (db (lit-negate^ d))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond a b c d cb db)
                     :exec (or (and (=30 a d)
                                    (=30 b cb))
                               (and (=30 a c)
                                    (=30 b db)))))
          (mv (lit-negate^ a) nil lit1 lit2))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond b a c d cb db)
                     :exec (or (and (=30 b d) (=30 a cb))
                               (and (=30 b c) (=30 a db)))))
          (mv (lit-negate^ b) nil lit1 lit2)))
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
         (id1 (lit->var^ lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         ((mv c d) (if both
                       (let ((id2 (lit->var^ lit2)))
                         (mv (gate-id->fanin0 id2 aignet)
                             (gate-id->fanin1 id2 aignet)))
                     (mv nil nil)))
         (negp1 (=b (lit->neg^ lit1) 1))
         (negp2 (=b (lit->neg^ lit2) 1))

         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 b c d lit2 negp2 both)
                          :exec
                          (or (=30 b lit2)                                      ;; substitution1
                              (and both (not negp2) (or (=30 b c) (=30 b d))))))) ;; substitution2
          (mv nil t (lit-negate^ a) lit2))
         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 a c d lit2 negp2 both)
                          :exec
                          (or (=30 a lit2)                                      ;; substitution1
                              (and both (not negp2) (or (=30 a c) (=30 a d))))))) ;; substitution2
          (mv nil t (lit-negate^ b) lit2))
         ((when (and both (=b 1 (b-and (lit->neg^ lit2) (b-not (lit->neg^ lit1))))
                     (mbe :logic (aignet-gate-simp-level3-cond2 a b c)
                          :exec (or (=30 c b) (=30 c a))))) ;; substitution2
          (mv nil t (lit-negate^ d) lit1))
         ((when  (and both (=b 1 (b-and (lit->neg^ lit2) (b-not (lit->neg^ lit1))))
                      (mbe :logic (aignet-gate-simp-level3-cond2 a b d)
                           :exec (or (=30 d b) (=30 d a))))) ;; substitution2
          (mv nil t (lit-negate^ c) lit1)))
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
         ((when (or (int= (lit->neg^ lit1) 1)
                    (int= (lit->neg^ lit2) 1)))
          (mv nil nil lit1 lit2))
         (id1 (lit->var^ lit1))
         (id2 (lit->var^ lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         ;; For each equality, we could either reduce the left or right gate.
         ;; Maybe experiment with this.  Atm. we'll prefer to reduce the
         ;; higher-numbered gate, lit1.
         ((when (mbe :logic (aignet-gate-simp-level4-cond a c d)
                     :exec (or (=30 a c) (=30 a d))))
          (mv nil t b lit2))
         ((when (mbe :logic (aignet-gate-simp-level4-cond b c d)
                     :exec (or (=30 b c) (=30 b d))))
          (mv nil t a lit2)))
      (mv nil nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-level4-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-open
                                          satlink::equal-of-make-lit)))
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

         ((when (or (< (the (integer 0 4) level) 2) neither))
          (mv nil nil lit1 lit2))

         ;; O2.
         ;; Only one direction possible since lit2 < lit1.
         ((mv level2-result & & &) (aignet-gate-simp-level2 lit1 lit2 both aignet))
         ((when level2-result)
          (mv level2-result nil lit1 lit2))

         ((when (< (the (integer 0 4) level) 3))
          (mv nil nil lit1 lit2))


         ;; O3.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level3 lit1 lit2 both aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2))

         ((when (or (< (the (integer 0 4) level) 4) (not both)))
          (mv nil nil lit1 lit2))

         ;; O4.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level4 lit1 lit2 aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2)))

      (mv nil nil lit1 lit2))

    :extra-args (level)
    :guard (and (natp level) (<= level 4))
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
    :guard (and (natp level) (<= level 4))
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

  (define aignet-addr-combine ((a :type (unsigned-byte 30))
                               (b :type (unsigned-byte 30)))
    :verify-guards nil
    (the (signed-byte 61)
         (- (the (signed-byte 61)
                 (logior (the (signed-byte 61)
                              (ash (the (signed-byte 31) a) 30))
                         (the (signed-byte 31) b))))))

  (local (in-theory (enable aignet-addr-combine)))

  (verify-guards aignet-addr-combine
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ash unsigned-byte-p))))
    :otf-flg t))

(defsection strash
  (defstobj strash
    (strashtab :type (hash-table eql))
    :inline t)

  ;; returns (mv exists key id).
  ;; exists implies that id is a gate with the two specified fanins.
  (define strash-lookup ((lit1 litp :type (unsigned-byte 30))
                         (lit2 litp :type (unsigned-byte 30))
                         strash aignet)
    :split-types t
    :inline t
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet))
    :returns (mv (found)
                 (key)
                 (id natp :rule-classes :type-prescription))
    (b* ((key (aignet-addr-combine (lit-fix lit1) (lit-fix lit2)))
         (id (strashtab-get key strash))
         ((when id)
          (b* (((unless (and (natp id)
                             (id-existsp id aignet)
                             (=2 (id->type id aignet) (gate-type))
                             (=30 (gate-id->fanin0 id aignet) (lit-fix lit1))
                             (=30 (gate-id->fanin1 id aignet) (lit-fix lit2))))
                (er hard? 'strash-lookup "Strash lookup found bogus value!")
                (mv nil key 0)))
            (mv t key id))))
      (mv nil key 0))
    ///

    (defthm strash-lookup-correct
      (b* (((mv found & id) (strash-lookup lit1 lit2 strash aignet)))
        (implies found
                 (and (aignet-idp id aignet)
                      (aignet-litp (mk-lit id bit) aignet)
                      (b* ((suff (lookup-id id aignet))
                           (node (car suff)))
                        (and (equal (stype node) (gate-stype))
                             (equal (fanin :gate0 suff)
                                    (lit-fix lit1))
                             (equal (fanin :gate1 suff)
                                    (lit-fix lit2)))))))
      :hints(("Goal" :in-theory (enable aignet-litp))))

    (defthm strash-lookup-id-type
      (natp (mv-nth 2 (strash-lookup lit1 lit2 strash aignet)))
      :rule-classes (:rewrite :type-prescription))

    (defthm strash-lookup-key-type
      (acl2-numberp (mv-nth 1 (strash-lookup lit1 lit2 strash aignet)))
      :rule-classes :type-prescription)

    (local (defret unsigned-byte-p-of-strash-lookup-1
             (implies (and found
                           (< (node-count aignet) #x1fffffff))
                      (unsigned-byte-p 29 id))
             :hints(("Goal" :in-theory (e/d (unsigned-byte-p aignet-idp)
                                            (lookup-id-consp-forward-to-id-bound))))))

    (defret unsigned-byte-p-of-strash-lookup
      (implies (and found
                    (< (node-count aignet) #x1fffffff)
                    (natp n)
                    (<= 29 n))
               (unsigned-byte-p n id))
      :hints(("Goal" :in-theory (e/d ()
                                     (unsigned-byte-p-of-strash-lookup-1
                                      strash-lookup))
              :use unsigned-byte-p-of-strash-lookup-1)))

    (defcong list-equiv equal (strash-lookup lit1 lit2 strash aignet) 4)))

(defsection gatesimp
  :parents (aignet-construction)
  :short "Structure encoding AIGNET construction settings for how much to try to
          simplify and whether to use hashing"
  :long "<p>A simple bit-encoded pair of @('level'), a natural number
determining how hard to try to simplify new AND nodes, and @('hashp'), a
Boolean value.  Created with @('(mk-gatesimp level hashp)'), field accessors
are @('(gatesimp-level gatesimp)') and @('(gatesimp-hashp gatesimp)').</p>

<p>The @('level') values correspond to the levels of simplification found in the paper:</p>
<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>
<p>Values of @('level') greater than 4 are treated the same as level 4.</p>"

  (define gatesimp-level-p (x)
    (and (natp x) (<= x 4))
    ///
    (define gatesimp-level-fix ((x gatesimp-level-p))
      :returns (new-x gatesimp-level-p)
      (mbe :logic (if (gatesimp-level-p x) x 4)
           :exec x)
      ///
      (defret gatesimp-level-fix-when-gatesimp-level-p
        (implies (gatesimp-level-p x) (equal new-x x)))

      (fty::deffixtype gatesimp-level :pred gatesimp-level-p :fix gatesimp-level-fix :equiv gatesimp-level-equiv
        :define t))

    (defthm gatesimp-level-p-compound-recognizer
      (implies (gatesimp-level-p x)
               (natp x))
      :rule-classes :compound-recognizer))

  (local (defthm unsigned-byte-p-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (unsigned-byte-p 3 x))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (local (defthm bound-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (<= x 4))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (fty::fixtype-to-bitstruct gatesimp-level :width 3)
  (fty::defbitstruct gatesimp
    ((hashp booleanp)
     (level gatesimp-level)))

  (defthm gatesimp->level-bound
    (<= (gatesimp->level x) 4)
    :rule-classes (:rewrite :linear)))

(defsection aignet-and-gate-simp/strash
  (def-gate-simp aignet-and-gate-simp/strash
    ;; BOZO The flag returned from this does not mean what it does in the
    ;; gate-simplifiers above. We use the second return value for the strash key
    ;; instead of the simplified flag, which is mainly used to stop iterating
    ;; when no simplification is found.
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((mv existing ?flg lit1 lit2)
          (aignet-gate-simp lit1 lit2 (gatesimp->level gatesimp) aignet))
         ((when existing)
          (mv existing nil lit1 lit2))
         ((when (not (gatesimp->hashp gatesimp)))
          (mv nil nil lit1 lit2))
         ((mv found ?key id) (strash-lookup lit1 lit2 strash aignet))
         ((when found)
          (mv (make-lit^ id 0) nil lit1 lit2)))
      (mv nil key lit1 lit2))

    :extra-args (gatesimp strash)
    :guard (gatesimp-p gatesimp)
    :xargs (:stobjs strash
            :guard-hints (("goal" :no-thanks t)))
    :eval-hints (("goal" :expand ((:free (id) (lit-eval (make-lit id 0) aignet-invals aignet-regvals aignet))
                                  (:free (lit1 lit2)
                                   (id-eval (mv-nth 2 (strash-lookup lit1 lit2 strash aignet)) aignet-invals aignet-regvals aignet)))))
    :skip-measure t
    :skip-precedes t)

  (defthm key-type-of-aignet-and-gate-simp/strash
    (or (not (mv-nth 1 (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet)))
        (acl2-numberp (mv-nth 1 (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet))))
    :hints(("Goal" :in-theory (enable aignet-and-gate-simp/strash)))
    :rule-classes :type-prescription)

  (fty::deffixequiv aignet-and-gate-simp/strash :args ((gatesimp gatesimp-p))))

(define aignet-hash-and ((lit1 litp :type (unsigned-byte 30) "Literal to AND with lit2")
                         (lit2 litp :type (unsigned-byte 30))
                         (gatesimp gatesimp-p :type (unsigned-byte 4)
                                   "Configuration for how much simplification to try and whether to use hashing")
                         (strash "Stobj containing the aignet's structural hash table")
                         aignet)
  :split-types t
  :parents (aignet-construction)
  :short "Add an AND node to an AIGNET, or find a node already representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet))
  :returns (mv (and-lit litp :rule-classes (:rewrite :type-prescription))
               (new-strash)
               (new-aignet))
  (b* ((lit1 (lit-fix lit1))
       (lit2 (lit-fix lit2))
       ((mv existing key lit1 lit2)
        (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet))
       ((when existing)
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv existing strash aignet)))
       (new-id (num-nodes aignet))
       (new-lit (make-lit new-id 0))
       (aignet (aignet-add-gate lit1 lit2 aignet))
       ((when (not key))
        (mv new-lit strash aignet))
       (strash (strashtab-put key new-id strash)))
    (mv new-lit strash aignet))

  ///

  (defthm litp-of-aignet-hash-and
    (litp (mv-nth 0 (aignet-hash-and lit1 lit2 gatesimp strash aignet))))

  (defmvtypes aignet-hash-and (natp nil nil))

  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-and lit1 lit2 gatesimp strash aignet) 3)

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
                               (eval-of-aignet-and-gate-simp/strash))
                   :use ((:instance eval-of-aignet-and-gate-simp/strash
                          (lit1 (lit-fix lit1))
                          (lit2 (lit-fix lit2))))))))


  (defthm stype-counts-preserved-of-aignet-hash-and
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype
                                 (mv-nth 2 (aignet-hash-and
                                            lit1 lit2 gatesimp strash aignet)))
                    (stype-count stype aignet))))

  (local (defret unsigned-byte-p-of-aignet-hash-and-1
           (implies (and (< (node-count aignet) #x1fffffff)
                         (aignet-litp lit1 aignet)
                         (aignet-litp lit2 aignet))
                    (unsigned-byte-p 31 and-lit))
           :hints (("goal" :use ((:instance unsigned-byte-p-when-aignet-litp
                                  (lit and-lit) (aignet new-aignet)))
                    :in-theory (disable unsigned-byte-p-when-aignet-litp)))))

  (defret unsigned-byte-p-of-aignet-hash-and
    (implies (and (< (node-count aignet) #x1fffffff)
                  (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet)
                  (natp n) (<= 31 n))
             (unsigned-byte-p n and-lit))
    :hints (("goal" :use unsigned-byte-p-of-aignet-hash-and-1
             :in-theory (disable unsigned-byte-p-of-aignet-hash-and-1)))))

(define aignet-install-and ((existing :type (or null (unsigned-byte 30)))
                            (key (or (not key) (acl2-numberp key)))
                            (lit1 litp :type (unsigned-byte 30))
                            (lit2 litp :type (unsigned-byte 30))
                            (strash)
                            (aignet))
  :split-types t
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet)
              (or (not existing)
                  (and (litp existing) (fanin-litp existing aignet))))
  :returns (mv (lit litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  (b* (((when existing)
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv (lit-fix existing) strash aignet)))
       (new-id (num-nodes aignet))
       (new-lit (mk-lit new-id 0))
       (aignet (aignet-add-gate lit1 lit2 aignet))
       ((when (not key)) (mv new-lit strash aignet))
       (strash (strashtab-put key new-id strash)))
    (mv new-lit strash aignet))
  ///

  (defthm aignet-install-and-of-aignet-and-gate-simp/strash
    (b* (((mv existing key nlit1 nlit2)
          (aignet-and-gate-simp/strash lit1 lit2 gatesimp strash aignet))) 
      (implies (equal existing1 existing)
               (equal (aignet-install-and existing1 key nlit1 nlit2 strash aignet)
                      (aignet-hash-and lit1 lit2 gatesimp strash aignet))))
    :hints(("Goal" :in-theory (enable aignet-hash-and)))))

(define aignet-populate-strash ((n natp)
                                (strash)
                                (aignet))
  :returns (new-strash)
  :guard (<= n (+ 1 (max-fanin aignet)))
  :measure (nfix (- (+ 1 (max-fanin aignet)) (nfix n)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((when (mbe :logic (zp (- (+ 1 (max-fanin aignet)) (nfix n)))
                   :exec (eql n (+ 1 (max-fanin aignet)))))
        strash)
       (slot0 (id->slot n 0 aignet))
       (type (snode->type slot0))
       ((unless (eql type (gate-type)))
        (aignet-populate-strash (+ 1 (lnfix n)) strash aignet))
       (lit0 (snode->fanin slot0))
       (lit1 (gate-id->fanin1 n aignet))
       ((mv foundp key ?id) (strash-lookup lit0 lit1 strash aignet))
       ((when foundp)
        (aignet-populate-strash (+ 1 (lnfix n)) strash aignet))
       (strash (strashtab-put key n strash)))
    (aignet-populate-strash (+ 1 (lnfix n)) strash aignet)))



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
                        (gatesimp gatesimp-p)
                        strash
                        aignet)
  :parents (aignet-construction)
  :short "Add a node to an AIGNET representing the OR of the given literals, or
find a node already representing the required logical expression."
  :long "<p>See @(see aignet-construction).</p>"
  :inline t
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  (b* (((mv lit strash aignet)
        (aignet-hash-and (lit-negate^ f0) (lit-negate^ f1) gatesimp strash aignet)))
    (mv (lit-negate^ lit) strash aignet))

  ///

  (def-aignet-preservation-thms aignet-hash-or)

  (defthm litp-aignet-hash-or
    (litp (mv-nth 0 (aignet-hash-or lit1 lit2 gatesimp strash aignet))))

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
                         (gatesimp gatesimp-p)
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
        (aignet-hash-and (lit-negate^ c) fb gatesimp strash aignet)))
    (aignet-hash-or c-tb nc-fb gatesimp strash aignet))

  ///

  (def-aignet-preservation-thms aignet-hash-mux)

  (defthm litp-aignet-hash-mux
    (litp (mv-nth 0 (aignet-hash-mux c tb fb gatesimp strash aignet))))

  ;; (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 2)
  ;; (defcong lit-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 3)
  ;; (defcong nat-equiv equal (aignet-hash-mux c tb fb gatesimp strash aignet) 4)

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
                         (gatesimp gatesimp-p)
                         strash
                         aignet)
  :inline t
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  (aignet-hash-mux f0 (lit-negate^ f1) f1 gatesimp strash aignet)

  ///

  (def-aignet-preservation-thms aignet-hash-xor)

  (defthm litp-aignet-hash-xor
    (litp (mv-nth 0 (aignet-hash-xor lit1 lit2 gatesimp strash aignet))))

  ;; (defcong lit-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 1)
  ;; (defcong lit-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 2)
  ;; (defcong nat-equiv equal (aignet-hash-xor f0 f1 gatesimp strash aignet) 3)

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



(define aignet-add-ins ((n natp) aignet)
  :returns (new-aignet)
  (if (zp n)
      (mbe :logic (non-exec (node-list-fix aignet))
           :exec aignet)
    (b* ((aignet (aignet-add-in aignet)))
      (aignet-add-ins (1- n) aignet)))
  ///
  (fty::deffixequiv aignet-add-ins)

  (def-aignet-preservation-thms aignet-add-ins)

  (std::defret pi-count-of-aignet-add-ins
    (equal (stype-count :pi new-aignet)
           (+ (nfix n) (stype-count :pi aignet))))

  (std::defret other-stype-count-of-aignet-add-ins
    (implies (not (equal (stype-fix stype) :pi))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (std::defret car-of-aignet-add-ins
    (implies (posp n)
             (equal (car new-aignet)
                    (pi-node)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret node-count-of-aignet-add-ins
    (equal (node-count new-aignet)
           (+ (nfix n) (node-count aignet))))

  (std::defret lookup-pi-of-aignet-add-ins
    (implies (< (nfix innum) (+ (nfix n) (stype-count :pi aignet)))
             (equal (lookup-stype innum :pi new-aignet)
                    (if (< (nfix innum) (stype-count :pi aignet))
                        (lookup-stype innum :pi aignet)
                      (aignet-add-ins (+ 1 (- (nfix innum) (stype-count :pi aignet))) aignet))))
    :hints(("Goal" :in-theory (e/d (lookup-stype) ((:d aignet-add-ins)))
            :expand (<call>
                     (:free (aignet) (aignet-add-ins 0 aignet))
                     (:free (n) (aignet-add-ins (+ 1 n) aignet)))
            :induct <call>)))

  (std::defret lookup-id-of-aignet-add-ins
    (implies (<= (nfix id) (+ (nfix n) (node-count aignet)))
             (equal (lookup-id id new-aignet)
                    (if (< (nfix id) (node-count aignet))
                        (lookup-id id aignet)
                      (aignet-add-ins (- (nfix id) (node-count aignet)) aignet))))
    :hints(("Goal" :in-theory (enable lookup-id))))

  (std::defret lookup-other-stype-of-aignet-add-ins
    (implies (not (equal (stype-fix stype) :pi))
             (equal (lookup-stype typenum stype (aignet-add-ins n aignet))
                    (lookup-stype typenum stype aignet))))
  

  (std::defret cdr-of-aignet-add-ins-when-posp
    (implies (posp n)
             (equal (cdr new-aignet)
                    (aignet-add-ins (1- n) aignet)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret lit-eval-of-aignet-add-ins
    (implies (and (<= (+ 1 (node-count aignet)) (nfix id))
                  (< id (+ 1 (nfix n) (node-count aignet))))
             (equal (lit-eval (mk-lit id neg) in-vals reg-vals new-aignet)
                    (b-xor neg
                           (nth (+ (num-ins aignet)
                                   (nfix id)
                                   (- (+ 1 (node-count aignet))))
                                in-vals))))
    :hints(("Goal"
            :expand ((:free (aignet) (id-eval id in-vals reg-vals aignet))
                     (:free (aignet) (lit-eval (mk-lit id neg) in-vals reg-vals aignet)))))))


(define aignet-add-regs ((n natp) aignet)
  :returns (new-aignet)
  (if (zp n)
      (mbe :logic (non-exec (node-list-fix aignet))
           :exec aignet)
    (b* ((aignet (aignet-add-reg aignet)))
      (aignet-add-regs (1- n) aignet)))
  ///
  (fty::deffixequiv aignet-add-regs)

  (def-aignet-preservation-thms aignet-add-regs)

  (std::defret reg-count-of-aignet-add-regs
    (equal (stype-count :reg new-aignet)
           (+ (nfix n) (stype-count :reg aignet))))

  (std::defret other-stype-count-of-aignet-add-regs
    (implies (not (equal (stype-fix stype) :reg))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (std::defret car-of-aignet-add-regs
    (implies (posp n)
             (equal (car new-aignet)
                    (reg-node)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret node-count-of-aignet-add-regs
    (equal (node-count new-aignet)
           (+ (nfix n) (node-count aignet))))

  (std::defret lookup-reg-of-aignet-add-regs
    (implies (< (nfix regnum) (+ (nfix n) (stype-count :reg aignet)))
             (equal (lookup-stype regnum :reg new-aignet)
                    (if (< (nfix regnum) (stype-count :reg aignet))
                        (lookup-stype regnum :reg aignet)
                      (aignet-add-regs (+ 1 (- (nfix regnum) (stype-count :reg aignet))) aignet))))
    :hints(("Goal" :in-theory (e/d (lookup-stype) ((:d aignet-add-regs)))
            :expand (<call>
                     (:free (aignet) (aignet-add-regs 0 aignet))
                     (:free (n) (aignet-add-regs (+ 1 n) aignet)))
            :induct <call>)))
  

  (std::defret lookup-id-of-aignet-add-regs
    (implies (<= (nfix id) (+ (nfix n) (node-count aignet)))
             (equal (lookup-id id new-aignet)
                    (if (< (nfix id) (node-count aignet))
                        (lookup-id id aignet)
                      (aignet-add-regs (- (nfix id) (node-count aignet)) aignet))))
    :hints(("Goal" :in-theory (enable lookup-id))))

  (std::defret lookup-other-stype-of-aignet-add-regs
    (implies (not (equal (stype-fix stype) :reg))
             (equal (lookup-stype typenum stype (aignet-add-regs n aignet))
                    (lookup-stype typenum stype aignet))))

  ;; (local (std::defret fanin-id-range-p-of-aignet-add-regs-lemma
  ;;          (fanin-id-range-p (+ 1 (node-count aignet)) n new-aignet)
  ;;          :hints(("Goal" :in-theory (enable fanin-id-range-p)))))

  ;; (std::defret fanin-id-range-p-of-aignet-add-regs
  ;;   (implies (equal id (+ 1 (node-count aignet)))
  ;;            (fanin-id-range-p id n new-aignet)))

  ;; (std::defret aignet-add-regs-preserves-fanin-id-range-p
  ;;   (implies (fanin-id-range-p id count aignet)
  ;;            (fanin-id-range-p id count new-aignet))
  ;;   :hints(("Goal" :in-theory (enable fanin-id-range-p))))

  (std::defret cdr-of-aignet-add-regs-when-posp
    (implies (posp n)
             (equal (cdr new-aignet)
                    (aignet-add-regs (1- n) aignet)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (std::defret lit-eval-of-aignet-add-regs
    (implies (and (<= (+ 1 (node-count aignet)) (nfix id))
                  (< id (+ 1 (nfix n) (node-count aignet))))
             (equal (lit-eval (mk-lit id neg) in-vals reg-vals new-aignet)
                    (b-xor neg
                           (nth (+ (num-regs aignet)
                                   (nfix id)
                                   (- (+ 1 (node-count aignet))))
                                reg-vals))))
    :hints(("Goal" :in-theory (enable lit-eval aignet-idp)
            :expand ((:free (aignet) (id-eval id in-vals reg-vals aignet))
                     (:free (aignet) (lit-eval (mk-lit id neg) in-vals reg-vals aignet)))))))
