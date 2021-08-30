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
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "std/util/termhints" :dir :system)
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :System))

(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

(std::make-returnspec-config :hints-sub-returnnames t)
(defstobj-clone litclasses litarr :strsubst (("LIT" . "LITCLASS")))
(defstobj-clone constmarks bitarr :strsubst (("BIT" . "AIGNET-CONSTMARKS")))





;; (define lit-directly-implies ((parent-lit litp)
;;                               (child-lit litp)
;;                               aignet)
;;   :guard (and (fanin-litp parent-lit aignet)
;;               (fanin-litp child-lit aignet))
;;   :measure (lit-id (aignet-lit-fix parent-lit aignet))
;;   :prepwork ((local (in-theory (disable lookup-id-out-of-bounds
;;                                         lookup-id-in-bounds-when-positive
;;                                         satlink::equal-of-lit-fix-backchain))))
;;   :hooks nil
;;   (b* ((parent-lit (mbe :logic (non-exec (aignet-lit-fix parent-lit aignet)) :exec parent-lit))
;;        (child-lit (mbe :logic (non-exec (aignet-lit-fix child-lit aignet)) :exec child-lit))
;;        ((when (int= (lit-fix parent-lit) (lit-fix child-lit))) t)
;;        ((when (int= (lit->neg parent-lit) 1)) nil)
;;        (parent-id (lit->var parent-lit))
;;        ((unless (and (int= (id->type parent-id aignet) (gate-type))
;;                      (eql 0 (id->regp parent-id aignet))))
;;         nil))
;;     (or (lit-directly-implies (gate-id->fanin0 parent-id aignet) child-lit aignet)
;;         (lit-directly-implies (gate-id->fanin1 parent-id aignet) child-lit aignet)))
;;   ///
;;   (local (in-theory (enable lit-eval-of-aignet-lit-fix)))

;;   (local (defthm equal-of-lit-fix-fwd
;;            (implies (equal (lit-fix x) y)
;;                     (lit-equiv x y))
;;            :rule-classes :forward-chaining))

;;   (defthm lit-directly-implies-of-aignet-lit-fix-parent
;;     (equal (lit-directly-implies (aignet-lit-fix parent-lit aignet) child-lit aignet)
;;            (lit-directly-implies parent-lit child-lit aignet)))
;;   (defthm lit-directly-implies-of-aignet-lit-fix-child
;;     (equal (lit-directly-implies parent-lit (aignet-lit-fix child-lit aignet) aignet)
;;            (lit-directly-implies parent-lit child-lit aignet)))

;;   (fty::deffixequiv lit-directly-implies
;;     :hints (("goal" :induct (lit-directly-implies parent-lit child-lit aignet)
;;                          :expand ((:free (child-lit aignet) (lit-directly-implies parent-lit child-lit aignet))
;;                                   (:free (child-lit aignet) (lit-directly-implies (lit-fix parent-lit) child-lit aignet))))))

;;   (local
;;    (defthmd not-lit-directly-implies-when-lit-eval-lemma
;;      (implies (and (aignet-litp parent-lit aignet)
;;                    (aignet-litp child-lit aignet))
;;               (implies (and (equal 1 (lit-eval parent-lit invals regvals aignet))
;;                             (equal 0 (lit-eval child-lit invals regvals aignet)))
;;                        (not (lit-directly-implies parent-lit child-lit aignet))))
;;      :hints (("goal" :induct (lit-directly-implies parent-lit child-lit aignet))
;;              (and stable-under-simplificationp
;;                   '(:expand ((lit-eval parent-lit invals regvals aignet)
;;                              (id-eval (lit->var parent-lit) invals regvals aignet))
;;                     :in-theory (enable eval-and-of-lits))))))

;;   (defthm not-lit-directly-implies-when-lit-eval
;;     (implies (and (equal 1 (lit-eval parent-lit invals regvals aignet))
;;                   (equal 0 (lit-eval child-lit invals regvals aignet)))
;;              (not (lit-directly-implies parent-lit child-lit aignet)))
;;     :hints (("goal" :use ((:instance not-lit-directly-implies-when-lit-eval-lemma
;;                            (parent-lit (aignet-lit-fix parent-lit aignet))
;;                            (child-lit (aignet-lit-fix child-lit aignet)))))))

;;   (defthm lit-directly-implies-transitive
;;     (implies (and (lit-directly-implies a b aignet)
;;                   (lit-directly-implies b c aignet))
;;              (lit-directly-implies a c aignet))
;;     :hints (("goal" :induct (lit-directly-implies a b aignet)
;;              :expand ((:free (b) (lit-directly-implies a b aignet))))))

;;   (defthm lit-directly-implies-self
;;     (lit-directly-implies x x aignet)))



(define id-is-xor ((id natp) aignet)
  :guard (id-existsp id aignet)
  :returns (mv is-xor
               (child1 litp :rule-classes :type-prescription)
               (child2 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds
                                        satlink::equal-of-lit-negate-backchain))))
  (b* (((unless (int= (id->type id aignet) (gate-type)))
        (mv nil 0 0))
       (f0 (gate-id->fanin0 id aignet))
       (f1 (gate-id->fanin1 id aignet))
       ((when (int= (id->regp id aignet) 1))
        ;; it's an explicit XOR gate
        (mv t f0 f1))
       ((unless (and (int= (lit-neg f0) 1)
                     (int= (lit-neg f1) 1)
                     (int= (id->type (lit-id f0) aignet) (gate-type))
                     (int= (id->regp (lit-id f0) aignet) 0)
                     (int= (id->type (lit-id f1) aignet) (gate-type))
                     (int= (id->regp (lit-id f1) aignet) 0)))
        (mv nil 0 0))
       (f00 (gate-id->fanin0 (lit-id f0) aignet))
       (f10 (gate-id->fanin1 (lit-id f0) aignet))
       (f01 (gate-id->fanin0 (lit-id f1) aignet))
       (f11 (gate-id->fanin1 (lit-id f1) aignet))
       (nf01 (lit-negate f01))
       (nf11 (lit-negate f11))
       ((when (or (and (int= f00 nf01)
                       (int= f10 nf11))
                  (and (int= f00 nf11)
                       (int= f10 nf01))))
        (mv t f00 f10)))
    (mv nil 0 0))
  ///
  (defret aignet-litp-of-<fn>
    (and (aignet-litp child1 aignet)
         (aignet-litp child2 aignet)))

  (defretd id-eval-when-id-is-xor
    (implies is-xor
             (equal (id-eval id in-vals reg-vals aignet)
                    (acl2::b-xor (lit-eval child1 in-vals reg-vals aignet)
                                 (lit-eval child2 in-vals reg-vals aignet))))
    :hints (("goal" :expand ((id-eval id in-vals reg-vals aignet)
                             (id-eval (lit-id (fanin 0 (lookup-id id aignet)))
                                      in-vals reg-vals aignet)
                             (id-eval (lit-id (fanin 1 (lookup-id id aignet)))
                                      in-vals reg-vals aignet))
             :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor)))))

  (defretd <fn>-not-xor-implies-and
    (implies (not is-xor)
             (iff (equal (ctype (stype (car (lookup-id id aignet)))) (gate-ctype))
                  (equal (stype (car (lookup-id id aignet))) (and-stype)))))

  (defret lit-id-bound-of-id-is-xor-child1
    (implies is-xor
             (< (lit->var child1) (nfix id)))
    :rule-classes :linear)

  (defret lit-id-bound-of-id-is-xor-child2
    (implies is-xor
             (< (lit->var child2) (nfix id)))
    :rule-classes :linear))


(define lit-is-xor ((lit litp) aignet)
  :guard (fanin-litp lit aignet)
  :returns (mv is-xor
               (child1 litp :rule-classes :type-prescription)
               (child2 litp :rule-classes :type-prescription))
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds
                                        satlink::equal-of-lit-negate-backchain))))
  (b* (((mv is-xor fanin0 fanin1) (id-is-xor (lit->var lit) aignet)))
    (mv is-xor (lit-negate-cond fanin0 (lit->neg lit)) fanin1))
  ///
  (defret aignet-litp-of-<fn>
    (and (aignet-litp child1 aignet)
         (aignet-litp child2 aignet)))

  (defretd lit-eval-when-lit-is-xor
    (implies is-xor
             (equal (lit-eval lit in-vals reg-vals aignet)
                    (acl2::b-xor (lit-eval child1 in-vals reg-vals aignet)
                                 (lit-eval child2 in-vals reg-vals aignet))))
    :hints (("goal" :expand ((lit-eval lit in-vals reg-vals aignet))
             :in-theory (enable id-eval-when-id-is-xor))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-xor)))))

  (defretd <fn>-not-xor-implies-and
    (implies (not is-xor)
             (iff (equal (ctype (stype (car (lookup-id (lit->var lit) aignet)))) (gate-ctype))
                  (equal (stype (car (lookup-id (lit->var lit) aignet))) (and-stype))))
    :hints(("Goal" :in-theory (enable id-is-xor-not-xor-implies-and))))

  (defret lit-id-bound-of-<fn>-child1
    (implies is-xor
             (< (lit->var child1) (lit->var lit)))
    :rule-classes :linear)

  (defret lit-id-bound-of-<fn>-child2
    (implies is-xor
             (< (lit->var child2) (lit->var lit)))
    :rule-classes :linear))

(local (defthm lookup-id-of-aignet-id-fix
         (Equal (lookup-id (aignet-id-fix id aignet) aignet)
                (lookup-id id aignet))
         :hints(("Goal" :in-theory (enable aignet-id-fix aignet-idp)))))


(defsection litclasses-orderedp
  (defun-sk litclasses-orderedp (litclasses)
    (forall id
            (implies (posp id)
                     (< (lit->var (nth-lit id litclasses)) id)))
    :rewrite :direct)

  (in-theory (disable litclasses-orderedp))

  (defthm litclasses-orderedp-implies-linear
    (implies (and (litclasses-orderedp litclasses)
                  (posp id))
             (< (lit->var (nth-lit id litclasses)) id))
    :rule-classes :linear)

  (defthm litclasses-orderedp-implies-lit-copy-linear
    (implies (and (litclasses-orderedp litclasses)
                  (posp (lit->var lit)))
             (< (lit->var (lit-copy lit litclasses)) (lit->var lit)))
    :hints(("Goal" :in-theory (enable lit-copy)))
    :rule-classes :linear)

  (defthm litclasses-orderedp-of-update-nth-lit
    (implies (and (litclasses-orderedp litclasses)
                  (< (lit->var lit) (nfix id)))
             (litclasses-orderedp (update-nth-lit id lit litclasses)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm litclasses-orderedp-of-resize-list
    (litclasses-orderedp (resize-list nil n 0))
    :hints(("Goal" :in-theory (enable litclasses-orderedp nth-lit)))))
             

;; (define lit-normal-form ((lit litp)
;;                          litclasses
;;                          constmarks)
;;   :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
;;               (< (lit->var lit) (lits-length litclasses))
;;               (< (lit->var lit) (bits-length constmarks)))
;;   :measure (lit->var lit)
;;   :returns (norm-lit litp :rule-classes :type-prescription)
;;   ;; Returns the normal form for lit.
;;   (b* ((id (lit->var lit))
;;        ((when (eql 0 id)) (lit-fix lit))
;;        ((when (eql 0 (get-bit id constmarks))) (lit-fix lit))
;;        (next-lit (lit-negate-cond (get-lit id litclasses) (lit->neg lit)))
;;        ((unless (mbt (< (lit->var next-lit) id)))
;;         (lit-fix lit)))
;;     (lit-normal-form next-lit litclasses constmarks))
;;   ///
;;   (defret lit-normal-form-bound
;;     (<= (lit->var norm-lit) (lit->var lit))
;;     :rule-classes :linear))

(define id-normal-form ((id natp)
                        constmarks
                        litclasses)
  :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
              (< id (lits-length litclasses))
              (< id (bits-length constmarks)))
  :measure (nfix id)
  :returns (norm-lit litp :rule-classes :type-prescription)
  ;; Returns the normal form for lit.
  (b* (((when (zp id)) (make-lit id 0))
       ((when (eql 0 (get-bit id constmarks))) (make-lit id 0))
       (next-lit (get-lit id litclasses))
       ((unless (mbt (< (lit->var next-lit) id)))
        (make-lit id 0)))
    (lit-negate-cond
     (id-normal-form (lit->var next-lit) constmarks litclasses)
     (lit->neg next-lit)))
  ///
  (defret id-normal-form-bound
    (<= (lit->var norm-lit) (nfix id))
    :rule-classes :linear)

  (defret id-normal-form-idempotent
    (equal (id-normal-form (lit->var (id-normal-form id constmarks litclasses))
                           constmarks litclasses)
           (make-lit (lit->var (id-normal-form id constmarks litclasses))
                     0)))

  (defthm id-normal-form-preserved-by-update-when-norm-different
    (implies (not (equal (lit->var (id-normal-form x constmarks litclasses))
                         (lit->var (id-normal-form y constmarks litclasses))))
             (equal (id-normal-form x constmarks (update-nth-lit y val litclasses))
                    (id-normal-form x constmarks litclasses)))
    :hints (("Goal" :in-theory (enable (:i id-normal-form))
             :induct (id-normal-form x constmarks litclasses)
             :expand ((:free (litclasses) (id-normal-form x constmarks litclasses))
                      (:free (litclasses) (id-normal-form 0 constmarks litclasses))))))

  (defthm id-normal-form-preserved-by-update-later
    (implies (< (nfix id) (nfix set-id))
             (equal (id-normal-form id constmarks (update-nth-lit set-id set-lit litclasses))
                    (id-normal-form id constmarks litclasses)))
    :hints (("Goal" :in-theory (enable (:i id-normal-form))
             :induct (id-normal-form id constmarks litclasses)
             :expand ((:free (litclasses) (id-normal-form id constmarks litclasses))
                      (:free (litclasses) (id-normal-form 0 constmarks litclasses))))))

  (defthm id-normal-form-preserved-by-update-to-normal-form
    (equal (id-normal-form x constmarks
                           (update-nth-lit y (id-normal-form y constmarks litclasses)
                                             litclasses))
           (id-normal-form x constmarks litclasses))
    :hints (("Goal" :in-theory (enable (:i id-normal-form))
             :induct (id-normal-form x constmarks litclasses)
             :expand ((:free (litclasses) (id-normal-form x constmarks litclasses))
                      (:free (litclasses) (id-normal-form 0 constmarks litclasses))))))

  (defthm id-normal-form-of-update-greater-constmark
    (implies (< (nfix x) (nfix y))
             (equal (id-normal-form x (update-nth y v constmarks) litclasses)
                    (id-normal-form x constmarks litclasses)))
    :hints (("Goal" :in-theory (enable (:i id-normal-form))
             :induct (id-normal-form x constmarks litclasses)
             :expand ((:free (constmarks litclasses) (id-normal-form x constmarks litclasses))
                      (:free (constmarks litclasses) (id-normal-form 0 constmarks litclasses))))))

  (defthmd id-normal-form-of-set-normal-form-id
    (implies (and (litclasses-orderedp litclasses)
                  (< (lit->var lit) (lit->var (id-normal-form x constmarks litclasses))))
             (equal (id-normal-form x
                                    (update-nth (lit->var (id-normal-form x constmarks litclasses)) 1 constmarks)
                                    (update-nth-lit (lit->var (id-normal-form x constmarks litclasses)) lit litclasses))
                    (lit-negate-cond (id-normal-form (lit->var lit) constmarks litclasses)
                                     (b-xor (lit->neg lit)
                                            (lit->neg (id-normal-form x constmarks litclasses))))))
    :hints (("Goal" :in-theory (enable (:i id-normal-form))
             :induct (id-normal-form x constmarks litclasses)
             :expand ((:free (constmarks litclasses) (id-normal-form x constmarks litclasses))
                      (:free (constmarks litclasses) (id-normal-form 0 constmarks litclasses))))))

  (defthm id-normal-form-of-set-normal-form-id-stronger
    (implies (and (litclasses-orderedp litclasses1)
                  (< (lit->var lit) (lit->var (id-normal-form x constmarks litclasses)))
                  (equal (id-normal-form x constmarks litclasses)
                         (id-normal-form x constmarks1 litclasses1)))
             (equal (id-normal-form x
                                    (update-nth (lit->var (id-normal-form x constmarks litclasses)) 1 constmarks1)
                                    (update-nth-lit (lit->var (id-normal-form x constmarks litclasses)) lit litclasses1))
                    (lit-negate-cond (id-normal-form (lit->var lit) constmarks1 litclasses1)
                                     (b-xor (lit->neg lit)
                                            (lit->neg (id-normal-form x constmarks litclasses))))))
    :hints (("goal" :do-not-induct t
             :use ((:instance id-normal-form-of-set-normal-form-id
                    (litclasses litclasses1) (constmarks constmarks1)))
             :in-theory (disable id-normal-form-of-set-normal-form-id)))))


(define lit-set-lit ((x litp)
                     (val litp)
                     litarr)
  :guard (< (lit->var x) (lits-length litarr))
  :inline t
  :enabled t
  (set-lit (lit->var x)
           (lit-negate-cond val (lit->neg x))
           litarr))


(local (defthm lit-negate-of-lit-negate-cond
         (equal (lit-negate (lit-negate-cond lit neg))
                (lit-negate-cond lit (b-not neg)))
         :hints(("Goal" :in-theory (enable lit-negate-cond b-not)))))

(define lit-normal-form ((lit litp) constmarks litclasses)
  :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
              (< (lit->var lit) (lits-length litclasses))
              (< (lit->var lit) (bits-length constmarks)))
  :returns (norm-lit litp)
  (lit-negate-cond
   (id-normal-form (lit->var lit) constmarks litclasses)
   (lit->neg lit))
  ///
  (defret lit-normal-form-bound
    (<= (lit->var norm-lit) (lit->var lit))
    :rule-classes :linear)

  (defret lit-normal-form-idempotent
    (equal (lit-normal-form (lit-normal-form lit constmarks litclasses)
                            constmarks litclasses)
           (lit-normal-form lit constmarks litclasses)))

  (defthm lit-normal-form-preserved-by-update-when-norm-different
    (implies (not (equal (lit->var (lit-normal-form x constmarks litclasses))
                         (lit->var (id-normal-form y constmarks litclasses))))
             (equal (lit-normal-form x constmarks (update-nth-lit y val litclasses))
                    (lit-normal-form x constmarks litclasses))))

  (local (in-theory (enable lit-set-lit)))

  (defthm lit-normal-form-preserved-by-update-when-norm-different-lit
    (implies (not (equal (lit->var (lit-normal-form x constmarks litclasses))
                         (lit->var (lit-normal-form y constmarks litclasses))))
             (equal (lit-normal-form x constmarks (lit-set-lit y val litclasses))
                    (lit-normal-form x constmarks litclasses))))

  (defthm lit-normal-form-preserved-by-update-later
    (implies (< (lit->var lit) (nfix set-id))
             (equal (lit-normal-form lit constmarks (update-nth-lit set-id lit-val litclasses))
                    (lit-normal-form lit constmarks litclasses))))

  (defthm lit-normal-form-preserved-by-update-later-lit
    (implies (< (lit->var lit) (lit->var set-lit))
             (equal (lit-normal-form lit constmarks (lit-set-lit set-lit lit-val litclasses))
                    (lit-normal-form lit constmarks litclasses))))

  (defthm lit-normal-form-preserved-by-update-to-normal-form
    (equal (lit-normal-form x constmarks
                           (update-nth-lit y (id-normal-form y constmarks litclasses)
                                             litclasses))
           (lit-normal-form x constmarks litclasses)))

  

  (local (defthm lit-negate-cond-reduce
           (equal (lit-negate-cond (lit-negate-cond x b) c)
                  (lit-negate-cond x (b-xor b c)))
           :hints(("Goal" :in-theory (enable lit-negate-cond)))))

  (local (defthm lit-negate-cond-0
           (equal (lit-negate-cond lit 0)
                  (lit-fix lit))))

  (defthm lit-normal-form-preserved-by-update-to-normal-form-lit
    (equal (lit-normal-form x constmarks
                           (lit-set-lit y (lit-normal-form y constmarks litclasses)
                                           litclasses))
           (lit-normal-form x constmarks litclasses)))

  (defthm lit-normal-form-of-update-greater-constmark
    (implies (< (lit->var x) (nfix y))
             (equal (lit-normal-form x (update-nth y v constmarks) litclasses)
                    (lit-normal-form x constmarks litclasses))))

  (defthmd lit-normal-form-of-set-normal-form-id
    (implies (and (litclasses-orderedp litclasses)
                  (< (lit->var lit) (lit->var (lit-normal-form x constmarks litclasses))))
             (equal (lit-normal-form x
                                    (update-nth (lit->var (lit-normal-form x constmarks litclasses)) 1 constmarks)
                                    (update-nth-lit (lit->var (lit-normal-form x constmarks litclasses)) lit litclasses))
                    (lit-negate-cond (lit-normal-form lit constmarks litclasses)
                                     (lit->neg (lit-normal-form x constmarks litclasses))))))

  (defthmd lit-normal-form-of-set-normal-form-lit
    (implies (and (litclasses-orderedp litclasses)
                  (< (lit->var lit) (lit->var (lit-normal-form x constmarks litclasses))))
             (equal (lit-normal-form x
                                     (update-nth (lit->var (lit-normal-form x constmarks litclasses)) 1 constmarks)
                                     (lit-set-lit (lit-normal-form x constmarks litclasses) lit litclasses))
                    (lit-normal-form lit constmarks litclasses))))

  (local (defthm equal-of-b-xor
           (equal (equal (b-xor a b) (b-xor a c))
                  (equal (bfix b) (bfix c)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm equal-of-lit-negate-cond
           (equal (equal (lit-negate-cond x a) (lit-negate-cond y a))
                  (equal (lit-fix x) (lit-fix y)))
           :hints(("Goal" :in-theory (enable lit-negate-cond
                                             satlink::equal-of-make-lit)))))

  (defthm lit-normal-form-of-set-normal-form-id-stronger
    (implies (and (litclasses-orderedp litclasses1)
                  (< (lit->var lit) (lit->var (lit-normal-form x constmarks litclasses)))
                  (equal (lit-normal-form x constmarks litclasses)
                         (lit-normal-form x constmarks1 litclasses1)))
             (equal (lit-normal-form x
                                    (update-nth (lit->var (lit-normal-form x constmarks litclasses)) 1 constmarks1)
                                    (update-nth-lit (lit->var (lit-normal-form x constmarks litclasses)) lit litclasses1))
                    (lit-negate-cond (lit-normal-form lit constmarks1 litclasses1)
                                     (lit->neg (lit-normal-form x constmarks litclasses)))))
    :hints (("goal" :do-not-induct t
             :use ((:instance lit-normal-form-of-set-normal-form-id
                    (litclasses litclasses1) (constmarks constmarks1)))
             :in-theory (disable lit-normal-form-of-set-normal-form-id))))

  (defthm lit-normal-form-of-set-normal-form-lit-stronger
    (implies (and (litclasses-orderedp litclasses1)
                  (< (lit->var lit) (lit->var (lit-normal-form x constmarks litclasses)))
                  (equal (lit-normal-form x constmarks litclasses)
                         (lit-normal-form x constmarks1 litclasses1)))
             (equal (lit-normal-form x
                                    (update-nth (lit->var (lit-normal-form x constmarks litclasses)) 1 constmarks1)
                                    (lit-set-lit (lit-normal-form x constmarks litclasses) lit litclasses1))
                    (lit-normal-form lit constmarks1 litclasses1)))
    :hints (("goal" :do-not-induct t
             :use ((:instance lit-normal-form-of-set-normal-form-lit
                    (litclasses litclasses1) (constmarks constmarks1)))
             :in-theory (disable lit-normal-form-of-set-normal-form-lit))))

  (defthm lit-normal-form-of-lit-negate-cond
    (equal (lit-normal-form (lit-negate-cond lit neg) constmarks litclasses)
           (lit-negate-cond (lit-normal-form lit constmarks litclasses) neg)))

  (defthm lit-normal-form-of-lit-negate
    (equal (lit-normal-form (lit-negate lit) constmarks litclasses)
           (lit-negate (lit-normal-form lit constmarks litclasses)))))




;; (define id-normal-form-shorten ((id natp)
;;                                 litclasses
;;                                 constmarks)
;;   :returns (mv (norm-lit (equal norm-lit (id-normal-form id constmarks litclasses))
;;                          :hints(("Goal" :in-theory (enable id-normal-form))))
;;                (new-litclasses (<= (len litclasses) (len new-litclasses)) :rule-classes :linear))
;;   :measure (nfix id)
;;   :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
;;               (< id (lits-length litclasses))
;;               (< id (bits-length constmarks)))
;;   :verify-guards :after-returns
;;   ;; Returns the normal form for lit and maps all lits encountered on its path
;;   ;; to that normal form.
;;   (b* (((when (zp id)) (mv (make-lit id 0) litclasses))
;;        ((when (eql 0 (get-bit id constmarks)))
;;         (mv (make-lit id 0) litclasses))
;;        (next-lit (get-lit id litclasses))
;;        ((unless (mbt (< (lit->var next-lit) id)))
;;         (mv (make-lit id 0) litclasses))
;;        ((mv norm-lit1 litclasses)
;;         (id-normal-form-shorten (lit->var next-lit) constmarks litclasses))
;;        (norm-lit (lit-negate-cond norm-lit1 (lit->neg next-lit)))
;;        (litclasses
;;         (set-lit id norm-lit litclasses)))
;;     (mv norm-lit litclasses))
;;   ///
;;   (local (in-theory (disable (:d id-normal-form-shorten))))

;;   (defret <fn>-preserves-litclasses-length
;;     (implies (< (nfix id) (len litclasses))
;;              (equal (len new-litclasses)
;;                     (len litclasses)))
;;     :hints (("goal" :induct <call>
;;              :expand (<call>))))

;;   (defret <fn>-preserves-litclasses-orderedp
;;     (implies (litclasses-orderedp litclasses)
;;              (litclasses-orderedp new-litclasses))
;;     :hints (("goal" :induct <call>
;;              :expand (<call>))))
  
;;   (local (defret <fn>-preserves-binding-when-other-id-normal-form
;;            (implies (not (equal (lit->var (id-normal-form x constmarks litclasses))
;;                                 (lit->var (id-normal-form id constmarks litclasses))))
;;                     (equal (nth-lit x new-litclasses)
;;                            (nth-lit x litclasses)))
;;            :hints (("goal" :induct <call>
;;                     :expand (<call>
;;                              (id-normal-form id constmarks litclasses))))))

;;   ;; (local (defret <fn>-binding-when-changed
;;   ;;          (implies (not (equal (nth-lit x new-litclasses)
;;   ;;                               (nth-lit x litclasses)))
;;   ;;                   (equal (lit->var (nth-lit x new-litclasses))
;;   ;;                          (lit->var (id-normal-form id constmarks litclasses))))
;;   ;;          :hints (("goal" :induct <call>
;;   ;;                   :expand (<call>
;;   ;;                            (id-normal-form id constmarks litclasses))))))

;;   (local (defret <fn>-binding-when-changed
;;            (implies (not (equal (nth-lit x new-litclasses)
;;                                 (nth-lit x litclasses)))
;;                     (equal (nth-lit x new-litclasses)
;;                            (id-normal-form x constmarks litclasses)))
;;            :hints (("goal" :induct <call>
;;                     :expand (<call>
;;                              (id-normal-form id constmarks litclasses))))))

;;   (local (defret id-normal-form-idempotent-free
;;            (implies (equal x (id-normal-form id constmarks litclasses))
;;                     (equal (id-normal-form (lit->var x)
;;                                            constmarks litclasses)
;;                            (make-lit (lit->var (id-normal-form id constmarks litclasses))
;;                                      0)))
;;            :fn id-normal-form))

;;   (defret <fn>-preserves-id-normal-form
;;     (equal (id-normal-form x new-constmarks litclasses)
;;            (id-normal-form x constmarks litclasses))
;;     :hints (("goal" :induct (id-normal-form x constmarks litclasses)
;;              :in-theory (enable (:i id-normal-form))
;;              :expand ((:free (litclasses) (id-normal-form x constmarks litclasses))
;;                       (:free (litclasses) (id-normal-form 0 constmarks litclasses))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((equal (nth-lit x new-litclasses)
;;                                   (nth-lit x litclasses)))))))

;;   (defret <fn>-preserves-lit-normal-form
;;     (equal (lit-normal-form x new-constmarks litclasses)
;;            (lit-normal-form x constmarks litclasses))
;;     :hints(("Goal" :in-theory (enable lit-normal-form)))))


;; (define lit-normal-form-shorten ((lit litp)
;;                                  litclasses
;;                                  constmarks)
;;   :returns (mv (norm-lit (equal norm-lit (lit-normal-form lit constmarks litclasses))
;;                          :hints(("Goal" :in-theory (enable lit-normal-form))))
;;                (new-litclasses (<= (len litclasses) (len new-litclasses)) :rule-classes :linear))
;;   :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
;;               (< (lit->var lit) (lits-length litclasses))
;;               (< (lit->var lit) (bits-length constmarks)))
;;   (b* (((mv lit1 litclasses) (id-normal-form-shorten (lit->var lit) constmarks litclasses)))
;;     (mv (lit-negate-cond lit1 (lit->neg lit)) litclasses))
;;   ///
;;   (defret <fn>-preserves-litclasses-length
;;     (implies (< (lit->var lit) (len litclasses))
;;              (equal (len new-litclasses)
;;                     (len litclasses))))

;;   (defret <fn>-preserves-litclasses-orderedp
;;     (implies (litclasses-orderedp litclasses)
;;              (litclasses-orderedp new-litclasses)))

;;   (defret <fn>-preserves-id-normal-form
;;     (equal (id-normal-form x new-constmarks litclasses)
;;            (id-normal-form x constmarks litclasses)))

;;   (defret <fn>-preserves-lit-normal-form
;;     (equal (lit-normal-form x new-constmarks litclasses)
;;            (lit-normal-form x constmarks litclasses))))



(define litclass-path-compress ((lit litp)
                                (target litp)
                                constmarks
                                litclasses)
  :guard (and (non-exec (ec-call (litclasses-orderedp litclasses)))
              (< (lit->var lit) (lits-length litclasses))
              (< (lit->var lit) (bits-length constmarks))
              (eql target (lit-normal-form lit constmarks litclasses)))
  :returns (new-litclasses (<= (len litclasses) (len new-litclasses))
                           :hints (("goal" :induct <call> :expand (<call>))))
  :verify-guards nil
  :measure (lit->var lit)
  (b* ((id (lit->var lit))
       ((when (zp id)) litclasses)
       ((when (eql 0 (get-bit id constmarks))) litclasses)
       (next-lit (lit-copy lit litclasses))
       ((unless (mbt (< (lit->var next-lit) (lit->var lit))))
        litclasses)
       (litclasses (lit-set-lit lit (mbe :logic (lit-normal-form lit constmarks litclasses)
                                         :exec target)
                                litclasses)))
    (litclass-path-compress next-lit target constmarks litclasses))
  ///

  (local (defthm lit-negate-cond-reduce
           (equal (lit-negate-cond (lit-negate-cond x b) b)
                  (lit-fix x))
           :hints(("Goal" :in-theory (enable lit-negate-cond)))))


  (local (defret <fn>-preserves-binding-when-other-id-normal-form
           (implies (not (equal (lit->var (id-normal-form x constmarks litclasses))
                                (lit->var (id-normal-form (lit->var lit) constmarks litclasses))))
                    (equal (nth-lit x new-litclasses)
                           (nth-lit x litclasses)))
           :hints (("goal" :induct <call>
                    :expand (<call>
                             (id-normal-form (lit->var lit) constmarks litclasses))))))

  (local (defthmd normalize-id-normal-form-of-lit->var
           (equal (id-normal-form (lit->var lit) constmarks litclasses)
                  (lit-negate-cond (lit-normal-form lit constmarks litclasses) (lit->neg lit)))
           :hints(("Goal" :in-theory (enable lit-normal-form)))))

  (local (defret <fn>-preserves-binding-when-other-lit-normal-form
           (implies (not (equal (lit->var (lit-normal-form x constmarks litclasses))
                                (lit->var (lit-normal-form lit constmarks litclasses))))
                    (equal (lit-copy x new-litclasses)
                           (lit-copy x litclasses)))
           :hints(("Goal" :in-theory (enable normalize-id-normal-form-of-lit->var lit-copy)))))

  (local (defret <fn>-binding-when-changed
           (implies (not (equal (nth-lit x new-litclasses)
                                (nth-lit x litclasses)))
                    (equal (nth-lit x new-litclasses)
                           (id-normal-form x constmarks litclasses)))
           :hints (("goal" :induct <call>
                    :expand (<call>
                             (id-normal-form id constmarks litclasses)))
                   (and stable-under-simplificationp
                        '(:cases ((equal (lit->var (id-normal-form x constmarks litclasses))
                                         (lit->var (id-normal-form (lit->var lit) constmarks litclasses))))
                          :in-theory (enable lit-normal-form))))))


  (local (defret id-normal-form-idempotent-free
           (implies (equal x (id-normal-form id constmarks litclasses))
                    (equal (id-normal-form (lit->var x)
                                           constmarks litclasses)
                           (make-lit (lit->var (id-normal-form id constmarks litclasses))
                                     0)))
           :fn id-normal-form))

  (defret litclass-path-compress-preserves-id-normal-form
    (equal (id-normal-form x constmarks new-litclasses)
           (id-normal-form x constmarks litclasses))
    :hints (("goal" :induct (id-normal-form x constmarks litclasses)
             :in-theory (enable (:i id-normal-form))
             :expand ((:free (litclasses) (id-normal-form x constmarks litclasses))
                      (:free (litclasses) (id-normal-form 0 constmarks litclasses))))
            (and stable-under-simplificationp
                 '(:cases ((equal (nth-lit x new-litclasses)
                                  (nth-lit x litclasses)))))))

  (defret litclass-path-compress-preserves-lit-normal-form
    (equal (lit-normal-form x constmarks new-litclasses)
           (lit-normal-form x constmarks litclasses))
    :hints (("goal" :in-theory (enable lit-normal-form))))

  (defret <fn>-preserves-litclasses-length
    (implies (< (lit->var lit) (len litclasses))
             (equal (len new-litclasses)
                    (len litclasses))))

  (defret <fn>-preserves-litclasses-orderedp
    (implies (litclasses-orderedp litclasses)
             (litclasses-orderedp new-litclasses))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:expand ((id-normal-form (lit->var lit) constmarks litclasses))
                   :in-theory (enable lit-normal-form)))))

  (verify-guards litclass-path-compress
    :hints ((and stable-under-simplificationp
                 '(:expand ((id-normal-form (lit->var lit) constmarks litclasses))
                   :in-theory (enable lit-copy lit-normal-form))))))

(local (defthm aignet-id-fix-bound
         (implies (natp id)
                  (<= (aignet-id-fix id aignet) id))
         :hints(("Goal" :in-theory (enable aignet-id-fix)))
         :rule-classes :linear))


(defsection litclasses-invar

  (defun-sk litclasses-invar (invals regvals constmarks litclasses aignet)
    (forall id
            (implies (and (aignet-idp id aignet)
                          (equal 1 (nth id constmarks)))
                     (equal (lit-eval (nth-lit id litclasses) invals regvals aignet)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable litclasses-invar))


  (defthm litclasses-invar-implies-id-eval
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-idp id aignet)
                  (equal 1 (nth id constmarks)))
             (equal (id-eval (lit->var (nth-lit id litclasses)) invals regvals aignet)
                    (b-xor (lit->neg (nth-lit id litclasses))
                           (id-eval id invals regvals aignet))))
    :hints (("goal" :use ((:instance litclasses-invar-necc))
             :in-theory (e/d (lit-eval) (litclasses-invar-necc)))))

  (defthm litclasses-invar-implies-eval-lit-copy
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-litp lit aignet)
                  (equal 1 (nth (lit->var lit) constmarks)))
             (equal (lit-eval (lit-copy lit litclasses) invals regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" :use ((:instance litclasses-invar-necc (id (lit->var lit))))
             :in-theory (e/d (lit-eval lit-copy) (litclasses-invar-necc)))))

  (defthm litclasses-invar-implies-id-normal-form
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-idp id aignet))
             (equal (lit-eval (id-normal-form id constmarks litclasses) invals regvals aignet)
                    (id-eval id invals regvals aignet)))
    :hints(("Goal" :in-theory (enable (:i id-normal-form) aignet-idp)
            :induct (id-normal-form id constmarks litclasses)
            :expand ((id-normal-form id constmarks litclasses)
                     (id-normal-form 0 constmarks litclasses)
                     (:free (neg) (lit-eval (make-lit id neg) invals regvals aignet))))))

  (defthm litclasses-invar-implies-lit-normal-form
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-litp lit aignet))
             (equal (lit-eval (lit-normal-form lit constmarks litclasses) invals regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-normal-form)
            :expand ((lit-eval lit invals regvals aignet)))))

  (defthm litclasses-invar-implies-id-eval-id-normal-form
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-idp id aignet))
             (equal (id-eval (lit->var (id-normal-form id constmarks litclasses)) invals regvals aignet)
                    (b-xor (lit->neg (id-normal-form id constmarks litclasses))
                           (id-eval id invals regvals aignet))))
    :hints (("goal" :use ((:instance litclasses-invar-implies-id-normal-form))
             :in-theory (e/d (lit-eval) (litclasses-invar-implies-id-normal-form)))))

  (local (in-theory (enable aignet-idp)))


  (defthm litclasses-invar-of-set-constmark
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (equal (id-eval id invals regvals aignet)
                         (lit-eval (nth-lit id litclasses) invals regvals aignet)))
             (litclasses-invar invals regvals
                               (update-nth id 1 constmarks)
                               litclasses aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))))

  (defthm litclasses-invar-of-set-litclasses
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (equal (id-eval id invals regvals aignet)
                         (lit-eval lit invals regvals aignet)))
             (litclasses-invar invals regvals
                               constmarks
                               (update-nth-lit id lit litclasses) aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))))


  (defthm litclasses-invar-of-lit-set-lit
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (equal (lit-eval lit1 invals regvals aignet)
                         (lit-eval lit invals regvals aignet)))
             (litclasses-invar invals regvals
                               constmarks
                               (lit-set-lit lit lit1 litclasses) aignet))
    :hints(("Goal" 
            :use ((:instance litclasses-invar-of-set-litclasses
                   (id (lit->var lit)) (lit (lit-negate-cond lit1 (lit->neg lit)))))
            :expand ((lit-eval lit invals regvals aignet))
            :in-theory (e/d (lit-set-lit)
                            (litclasses-invar-of-set-litclasses)))))

  (defthm litclasses-invar-of-lit-set-lit-and-constmark
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (equal (lit-eval lit1 invals regvals aignet)
                         (lit-eval lit invals regvals aignet)))
             (litclasses-invar invals regvals
                               (update-nth (lit->var lit) 1 constmarks)
                               (lit-set-lit lit lit1 litclasses) aignet))
    :hints (("goal" :use ((:instance litclasses-invar-of-set-constmark
                           (id (lit->var lit))
                           (litclasses (lit-set-lit lit lit1 litclasses)))
                          litclasses-invar-of-lit-set-lit)
             :in-theory (e/d (lit-set-lit)
                             (litclasses-invar-of-set-constmark
                              litclasses-invar-of-lit-set-lit))
             :expand ((lit-eval lit invals regvals aignet)))))

  (local (in-theory (disable lit-set-lit)))

  (defthm litclasses-invar-of-path-compress
    (implies (litclasses-invar invals regvals constmarks litclasses aignet)
             (litclasses-invar  invals regvals constmarks
                                (litclass-path-compress lit target constmarks litclasses)
                                aignet))
    :hints(("Goal" :in-theory (enable (:i litclass-path-compress))
            :induct (litclass-path-compress lit target constmarks litclasses)
            :expand ((litclass-path-compress lit target constmarks litclasses)))
           (and stable-under-simplificationp
                '(:in-theory (enable lit-eval lit-set-lit)))
           (and stable-under-simplificationp
                (let ((lit (assoc 'litclasses-invar clause)))
                  (and lit
                       `(:expand (,lit)))))))

  (defthm litclasses-invar-of-empty-constmarks
    (litclasses-invar invals regvals (resize-list nil n 0) litclasses aignet)
    :hints(("Goal" :in-theory (enable litclasses-invar)))))

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
    (marks-boundedp limit (resize-list nil n 0)))

  (defthm marks-boundedp-by-len
    (implies (<= (len x) (nfix limit))
             (marks-boundedp limit x))))

(defines aignet-mark-const-nodes-rec
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds
                                        satlink::equal-of-lit-negate-backchain
                                        acl2::nth-when-too-large-cheap
                                        acl2::zp-when-gt-0
                                        default-car default-cdr
                                        satlink::equal-of-lit-negate-cond-component-rewrites
                                        satlink::equal-of-lit-negate-component-rewrites))))

  (define aignet-mark-const-nodes-class ((lit litp :type (integer 0 *))
                                         aignet
                                         ;; mark
                                         constmarks
                                         litclasses)
    ;; This function does the memoization gatekeeping, stopping if lit has
    ;; already been traversed (which is signalled by its constmark and next-lit
    ;; being 1).
    :guard (and (fanin-litp lit aignet)
              (< (lit-id lit) (bits-length constmarks))
              (< (lit-id lit) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :split-types t
  :measure (acl2::two-nats-measure (lit->var lit) 2)
  :returns (mv contra new-constmarks new-litclasses)
  :verify-guards nil
  (b* ((id (lit->var lit))
       ((when (zp id))
        (acl2::hintcontext :constlit
                           (mv (eql (lit->neg lit) 0) constmarks litclasses)))
       (constmark (get-bit id constmarks))
       ;; Get the next lit in the class first, because otherwise it'll be 1.
       (next-lit (lit-copy lit litclasses))
       ((when (acl2::and** (eql 1 constmark)
                           (eql 0 (lit->var next-lit))))
        ;; Two cases here.
        ;; 1. If next-lit is 0, then we have a contradiction/

        ;; 2. If next-lit is 1, we have already traversed this node.  We ensure
        ;; that we only set a literal to a constant by calling this function on
        ;; it (or its negation), which sets it to 1 just before beginning to
        ;; traverse it.
        (acl2::hintcontext :const-nextlit
                           (mv (eql 0 (lit->neg next-lit)) constmarks litclasses)))
       (constmarks (set-bit id 1 constmarks))
       (litclasses (lit-set-lit lit 1 litclasses))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-rec lit aignet constmarks litclasses))
       ((when contra) (mv t constmarks litclasses))
       ((unless (acl2::and** (eql 1 constmark)
                      (mbt (< (lit->var next-lit) (lit->var lit)))))
        (mv nil constmarks litclasses)))
    (aignet-mark-const-nodes-class next-lit aignet constmarks litclasses)))
       
  (define aignet-mark-const-nodes-rec ((lit litp :type (integer 0 *))
                                       aignet
                                       ;; mark ;; marks nodes already visited (all equivalent to 1)
                                       constmarks ;; marks valid entries in litclasses
                                       litclasses)
  :guard (and (fanin-litp lit aignet)
              ;; (< (lit-id lit) (bits-length mark))
              (< (lit-id lit) (bits-length constmarks))
              (< (lit-id lit) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :split-types t
  :measure (acl2::two-nats-measure (lit->var lit) 1)
  :returns (mv contra new-constmarks new-litclasses)
  
  (b* ((id (lit->var lit))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0))
       ((unless (int= type (gate-type)))
        (mv nil constmarks litclasses))
       (slot1 (id->slot id 1 aignet))
       ((unless (acl2::and** (int= (lit->neg lit) 0)
                             (int= (snode->regp slot1) 0))) ;; not xor
        (aignet-mark-const-nodes-xor lit aignet constmarks litclasses))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class (snode->fanin slot0) aignet constmarks litclasses))
       ((when contra) (mv t constmarks litclasses))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class (snode->fanin slot1) aignet constmarks litclasses))
       ((when contra) (mv t constmarks litclasses)))
    (aignet-mark-const-nodes-xor lit aignet constmarks litclasses)))

  (define aignet-mark-const-nodes-xor ((lit litp :type (integer 0 *))
                                       aignet
                                       ;; mark ;; marks nodes already visited (all equivalent to 1)
                                       constmarks ;; marks valid entries in litclasses
                                       litclasses)
  :guard (and (fanin-litp lit aignet)
              (eql (id->type (lit->var lit) aignet) (gate-type))
              ;; (< (lit-id lit) (bits-length mark))
              (< (lit-id lit) (bits-length constmarks))
              (< (lit-id lit) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :split-types t
  :measure (acl2::two-nats-measure (lit->var lit) 0)
  :returns (mv contra new-constmarks new-litclasses)
  (b* (((mv is-xor xor-fanin0 xor-fanin1) (lit-is-xor lit aignet))
       ((unless is-xor)
        (mv nil constmarks litclasses))

       (norm-fanin0 (lit-normal-form xor-fanin0 constmarks litclasses))
       (norm-fanin1 (lit-normal-form xor-fanin1 constmarks litclasses))

       ;; We have an XOR.  We are assuming this XOR is true which means
       ;; xor-fanin0 is the negation of xor-fanin1, and therefore norm-fanin0
       ;; is the negation of norm-fanin1.

       ((when (int= (lit->var norm-fanin0) (lit->var norm-fanin1)))
        ;; If the two norm fanins are explicit negations, there's nothing to
        ;; do.  If they are equal, we have a contradiction.
        (acl2::hintcontext :xorcontra
                           (mv (int= (lit->neg norm-fanin0) (lit->neg norm-fanin1))
                               constmarks litclasses)))

       ;; Now we want to set one class to the negation of the other class.
       ;; Find which has the lesser normal form.
       ((mv norm-fanin unnorm-norm-fanin upd-norm-fanin upd-fanin)
        (if (< (lit->var norm-fanin0) (lit->var norm-fanin1))
            (mv norm-fanin0 xor-fanin0 norm-fanin1 xor-fanin1)
          (mv norm-fanin1 xor-fanin1 norm-fanin0 xor-fanin0)))

       (litclasses (litclass-path-compress unnorm-norm-fanin norm-fanin constmarks litclasses))

       ((when (int= (lit->var norm-fanin) 0))
        (b* ((consttrue-class (lit-negate-cond upd-fanin (lit->neg norm-fanin))))
          (acl2::hintcontext :constclass
                             ;; Setting upd-fanin (and its class) to a constant.  Do this by calling
                             ;; aignet-mark-const-nodes-class on either upd-fanin or its negation.
                             (aignet-mark-const-nodes-class consttrue-class
                                                            aignet constmarks litclasses))))

       ;; Set upd-fanin (and its class) to the negation of norm-fanin.
       (litclasses (lit-set-lit upd-norm-fanin (lit-negate norm-fanin) litclasses))
       (constmarks (set-bit (lit->var upd-norm-fanin) 1 constmarks))
       (litclasses (litclass-path-compress upd-fanin (lit-negate norm-fanin) constmarks litclasses)))

    (acl2::hintcontext :xorclass
                       (mv nil constmarks litclasses))))
  ///

  (local (in-theory (disable aignet-mark-const-nodes-class
                             aignet-mark-const-nodes-rec
                             aignet-mark-const-nodes-xor)))
  ;; (local (defthm mv-nth-of-cons
  ;;          (implies (syntaxp (quotep n))
  ;;                   (equal (mv-nth n (cons a b))
  ;;                          (if (zp n) a
  ;;                            (mv-nth (1- n) b))))
  ;;          :hints(("Goal" :in-theory (enable mv-nth)))))

  (std::defret-mutual aignet-mark-const-nodes-preserves-litclasses-orderedp
    (defret aignet-mark-const-nodes-class-preserves-litclasses-orderedp
      (implies (litclasses-orderedp litclasses)
               (litclasses-orderedp new-litclasses))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-class)
    (defret aignet-mark-const-nodes-rec-preserves-litclasses-orderedp
      (implies (litclasses-orderedp litclasses)
               (litclasses-orderedp new-litclasses))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-rec)
    (defret aignet-mark-const-nodes-xor-preserves-litclasses-orderedp
      (implies (litclasses-orderedp litclasses)
               (litclasses-orderedp new-litclasses))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-xor))

  (std::defret-mutual aignet-mark-const-nodes-preserves-litclasses-size
    (defret aignet-mark-const-nodes-class-preserves-litclasses-size
      (implies (< (lit->var lit) (len litclasses))
               (equal (len new-litclasses)
                      (len litclasses)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-class)
    (defret aignet-mark-const-nodes-rec-preserves-litclasses-size
      (implies (< (lit->var lit) (len litclasses))
               (equal (len new-litclasses)
                      (len litclasses)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-rec)
    (defret aignet-mark-const-nodes-xor-preserves-litclasses-size
      (implies (< (lit->var lit) (len litclasses))
               (equal (len new-litclasses)
                      (len litclasses)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-xor))

  (std::defret-mutual aignet-mark-const-nodes-preserves-constmarks-size
    (defret aignet-mark-const-nodes-class-preserves-constmarks-size
      (implies (< (lit->var lit) (len constmarks))
               (equal (len new-constmarks)
                      (len constmarks)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-class)
    (defret aignet-mark-const-nodes-rec-preserves-constmarks-size
      (implies (< (lit->var lit) (len constmarks))
               (equal (len new-constmarks)
                      (len constmarks)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-rec)
    (defret aignet-mark-const-nodes-xor-preserves-constmarks-size
      (implies (< (lit->var lit) (len constmarks))
               (equal (len new-constmarks)
                      (len constmarks)))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-xor))


  (local (defthm lit-negate-cond-of-lit-negate-cond
           (equal (lit-negate-cond (lit-negate-cond lit neg1) neg2)
                  (lit-negate-cond lit (b-xor neg1 neg2)))
           :hints(("Goal" :in-theory (enable lit-negate-cond b-xor b-not)))))

  (verify-guards aignet-mark-const-nodes-class
    :hints(("Goal" :in-theory (enable aignet-idp))))


  (local (in-theory (disable lit-set-lit)))
  (local (in-theory (enable aignet-idp)))

  (local (defthm b-xor-equal-1
           (equal (equal 1 (b-xor a b))
                  (equal (bfix a) (b-not b)))
           :hints(("Goal" :in-theory (enable b-xor b-not)))))
                                  
  (local (defthm equal-of-b-not
           (implies (and (equal (b-not x) y)
                         (bitp x))
                    (equal (equal x (b-not y)) t))))

  (local (defun lit-hq (x) (lit-fix x)))
  (local (fty::deffixcong lit-equiv equal (lit-hq x) x))
  (local (in-theory (disable lit-hq (lit-hq) (:t lit-hq))))
  (local (acl2::termhint-add-quotesym lit-hq))


  (local (defthm lit-eval-when-and-stype
           (implies (and (equal (stype (car (lookup-id (lit->var lit) aignet))) :and)
                         (equal (lit->neg lit) 0))
                    (equal (lit-eval lit invals regvals aignet)
                           (b-and (lit-eval (fanin 0 (lookup-id (lit->var lit) aignet))
                                             invals regvals aignet)
                                  (lit-eval (fanin 1 (lookup-id (lit->var lit) aignet))
                                             invals regvals aignet))))
           :hints(("Goal" :in-theory (enable lit-eval id-eval eval-and-of-lits)))))

  (std::defret-mutual aignet-mark-const-nodes-preserves-litclasses-invar
    (defret aignet-mark-const-nodes-class-preserves-litclasses-invar
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-class)
    (defret aignet-mark-const-nodes-rec-preserves-litclasses-invar
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-rec)
    (defret aignet-mark-const-nodes-xor-preserves-litclasses-invar
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
      :hints ('(:expand (<call>))
              (acl2::function-termhint
               aignet-mark-const-nodes-xor
               (:xorclass
                '(:in-theory (enable lit-eval-when-lit-is-xor
                                     id-eval-when-id-is-xor)))
               (:constclass
                `(:computed-hint-replacement
                  ((and stable-under-simplificationp
                        '(:error t)))
                  :use ((:instance litclasses-invar-implies-lit-normal-form
                         (lit ,(lit-hq unnorm-norm-fanin))))
                  :expand ((lit-eval ,(lit-hq norm-fanin) invals regvals aignet))
                  :in-theory (e/d (lit-eval-when-lit-is-xor)
                                  (litclasses-invar-implies-lit-normal-form))))))
      :fn aignet-mark-const-nodes-xor))

  (std::defret-mutual aignet-mark-const-nodes-contradiction-correct
    (defret aignet-mark-const-nodes-class-contra-correct
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (not contra))
      :hints ('(:expand (<call>))
              (acl2::function-termhint
               aignet-mark-const-nodes-class
               (:constlit '(:expand ((lit-eval lit invals regvals aignet))))
               (:const-nextlit
                `(:use ((:instance litclasses-invar-implies-eval-lit-copy))
                  :expand ((lit-eval ,(lit-hq next-lit) invals regvals aignet))
                  :in-theory (disable litclasses-invar-implies-eval-lit-copy)))))
      :fn aignet-mark-const-nodes-class)
    (defret aignet-mark-const-nodes-rec-contra-correct
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (not contra))
      :hints ('(:expand (<call>)))
      :fn aignet-mark-const-nodes-rec)
    (defret aignet-mark-const-nodes-xor-contra-correct
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (lit-eval lit invals regvals aignet))
                    (aignet-litp lit aignet))
               (not contra))
      :hints ('(:expand (<call>))
              (acl2::function-termhint
               aignet-mark-const-nodes-xor
               (:xorcontra
                `(:computed-hint-replacement
                  ((and stable-under-simplificationp
                        '(:error t)))
                  :use ((:instance litclasses-invar-implies-lit-normal-form
                         (lit ,(lit-hq xor-fanin0)))
                        (:instance litclasses-invar-implies-lit-normal-form
                         (lit ,(lit-hq xor-fanin1))))
                  :in-theory (e/d (lit-eval-when-lit-is-xor)
                                  (litclasses-invar-implies-lit-normal-form))))
               (:constclass
                `(:computed-hint-replacement
                  ((and stable-under-simplificationp
                        '(:error t)))
                  :use ((:instance litclasses-invar-implies-lit-normal-form
                         (lit ,(lit-hq unnorm-norm-fanin))))
                  :expand ((lit-eval ,(lit-hq norm-fanin) invals regvals aignet))
                  :in-theory (e/d (lit-eval-when-lit-is-xor)
                                  (litclasses-invar-implies-lit-normal-form))))))
      :fn aignet-mark-const-nodes-xor))

  (fty::deffixequiv-mutual aignet-mark-const-nodes-rec))


(define aignet-mark-const-nodes-class-list ((lits lit-listp)
                                            aignet
                                            constmarks
                                            litclasses)
  :guard (and (aignet-lit-listp lits aignet)
              (< (lits-max-id-val lits) (bits-length constmarks))
              (< (lits-max-id-val lits) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :returns (mv contra new-constmarks new-litclasses)
  (b* (((when (atom lits))
        (mv nil constmarks litclasses))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class (car lits) aignet constmarks litclasses))
       ((when contra)
        (mv t constmarks litclasses)))
    (aignet-mark-const-nodes-class-list (cdr lits) aignet constmarks litclasses))
  ///
  (defret <fn>-preserves-litclasses-orderedp
    (implies (litclasses-orderedp litclasses)
             (litclasses-orderedp new-litclasses))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-preserves-litclasses-size
    (implies (< (lits-max-id-val lits) (len litclasses))
             (equal (len new-litclasses)
                    (len litclasses)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable lits-max-id-val))))

  (defret <fn>-preserves-constmarks-size
    (implies (< (lits-max-id-val lits) (len constmarks))
             (equal (len new-constmarks)
                    (len constmarks)))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable lits-max-id-val))))

  (defret <fn>-preserves-litclasses-invar
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (equal 1 (aignet-eval-conjunction lits invals regvals aignet))
                  (aignet-lit-listp lits aignet))
             (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-lit-listp aignet-eval-conjunction)
             :expand (<call>))))

  (defret aignet-mark-const-nodes-class-list-contra-correct
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (equal 1 (aignet-eval-conjunction lits invals regvals aignet))
                    (aignet-lit-listp lits aignet))
               (not contra))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-lit-listp aignet-eval-conjunction)
             :expand (<call>)))))
  
(define aignet-mark-const-nodes-propagate ((n posp)
                                           updatedp
                                           aignet
                                           constmarks
                                           litclasses)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :measure (nfix (- (num-fanins aignet) (pos-fix n)))
  :returns (mv contra new-updatedp new-constmarks new-litclasses)
  (b* ((n (lposfix n))
       ((when (mbe :logic (zp (- (num-fanins aignet) n))
                   :exec (eql (num-fanins aignet) n)))
        (mv nil updatedp constmarks litclasses))
       (norm-lit (id-normal-form n constmarks litclasses))
       ((unless (acl2::and** (eql (lit->var norm-lit) 0)
                             (not (equal (lit->var (get-lit n litclasses)) 0))))
        (aignet-mark-const-nodes-propagate (1+ n) updatedp aignet constmarks litclasses))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class (make-lit n (b-not (lit->neg norm-lit)))
                                       aignet constmarks litclasses))
       ((when contra)
        (mv t t constmarks litclasses)))
    (aignet-mark-const-nodes-propagate (1+ n) t aignet constmarks litclasses))
  ///

  (defret <fn>-preserves-litclasses-orderedp
    (implies (litclasses-orderedp litclasses)
             (litclasses-orderedp new-litclasses))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (defret <fn>-preserves-litclasses-size
    (implies (< (fanin-count aignet) (len litclasses))
             (equal (len new-litclasses)
                    (len litclasses)))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (defret <fn>-preserves-constmarks-size
    (implies (< (fanin-count aignet) (len constmarks))
             (equal (len new-constmarks)
                    (len constmarks)))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (local (defthm lit-eval-of-make-lit-not-eval
           (implies (equal neg (id-eval id invals regvals aignet))
                    (equal (lit-eval (make-lit id (b-not neg)) invals regvals aignet) 1))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (defret <fn>-preserves-litclasses-invar
    (implies (litclasses-invar invals regvals constmarks litclasses aignet)
             (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
    :hints (("Goal" :expand (<call>)
             :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance litclasses-invar-implies-id-normal-form
                          (id (pos-fix n))))
                   :expand ((lit-eval (id-normal-form (pos-fix n) constmarks litclasses)
                                      invals regvals aignet))
                   :in-theory (disable litclasses-invar-implies-id-normal-form)))))

  (defret <fn>-contra-correct
    (implies (litclasses-invar invals regvals constmarks litclasses aignet)
             (not contra))
    :hints (("Goal" :expand (<call>)
             :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance litclasses-invar-implies-id-normal-form
                          (id (pos-fix n))))
                   :expand ((lit-eval (id-normal-form (pos-fix n) constmarks litclasses)
                                      invals regvals aignet))
                   :in-theory (disable litclasses-invar-implies-id-normal-form))))))

(define aignet-mark-const-nodes-fixpoint ((limit natp)
                                          aignet
                                          constmarks
                                          litclasses)
  :guard (and (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (non-exec (ec-call (litclasses-orderedp litclasses))))
  :measure (nfix limit)
  :returns (mv contra new-constmarks new-litclasses)
  (b* (((when (zp limit))
        (cw "Note: recursion limit ran out in ~x0~%" std::__function__)
        (mv nil constmarks litclasses))
       ((mv contra updatedp constmarks litclasses)
        (aignet-mark-const-nodes-propagate 1 nil aignet constmarks litclasses))
       ((when (or contra (not updatedp)))
        (mv contra constmarks litclasses)))
    (aignet-mark-const-nodes-fixpoint (1- limit) aignet constmarks litclasses))
  ///

  (defret <fn>-preserves-litclasses-orderedp
    (implies (litclasses-orderedp litclasses)
             (litclasses-orderedp new-litclasses))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (defret <fn>-preserves-litclasses-size
    (implies (< (fanin-count aignet) (len litclasses))
             (equal (len new-litclasses)
                    (len litclasses)))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (defret <fn>-preserves-constmarks-size
    (implies (< (fanin-count aignet) (len constmarks))
             (equal (len new-constmarks)
                    (len constmarks)))
    :hints (("Goal" :expand (<call>)
             :induct <call>)))

  (defret <fn>-preserves-litclasses-invar
    (implies (litclasses-invar invals regvals constmarks litclasses aignet)
             (litclasses-invar invals regvals new-constmarks new-litclasses aignet)))

  (defret <fn>-contra-correct
    (implies (litclasses-invar invals regvals constmarks litclasses aignet)
             (not contra))))



(define aignet-mark-const-nodes-top ((lit litp)
                                     aignet
                                     constmarks
                                     litclasses)
  :guard (and (non-exec (equal constmarks (acl2::create-bitarr)))
              (non-exec (equal litclasses (create-litarr)))
              (fanin-litp lit aignet))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  :returns (mv contra new-constmarks new-litclasses)
  (b* ((constmarks (mbe :logic (non-exec (acl2::create-bitarr)) :exec constmarks))
       (constmarks (resize-bits (num-fanins aignet) constmarks))
       (litclasses (mbe :logic (non-exec (create-litarr)) :exec litclasses))
       (litclasses (resize-lits (num-fanins aignet) litclasses))
       (lit (mbe :logic (non-exec (aignet-lit-fix lit aignet)) :exec lit))
       ((acl2::hintcontext-bind ((orig-constmarks constmarks)
                                 (orig-litclasses litclasses))))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class lit aignet constmarks litclasses))
       ((when contra)
        (acl2::hintcontext
         :contra
         (mv contra constmarks litclasses)))
       ((acl2::hintcontext :pass1)))
    (aignet-mark-const-nodes-fixpoint 10 aignet constmarks litclasses))
  ///

  (defret litclasses-orderedp-of-<fn>
    (litclasses-orderedp new-litclasses))

  (defret litclasses-size-of-<fn>
    (equal (len new-litclasses)
           (num-fanins aignet))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret constmarks-size-of-<fn>
    (equal (len new-constmarks)
           (num-fanins aignet))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret litclasses-invar-of-<fn>
    (implies (equal (lit-eval lit invals regvals aignet) 1)
             (litclasses-invar invals regvals new-constmarks new-litclasses aignet)))

  (set-ignore-ok t)

  (defret <fn>-contra-correct
    (implies (equal (lit-eval lit invals regvals aignet) 1)
             (not contra))
    :hints ((acl2::function-termhint
             aignet-mark-const-nodes-top
             (:contra
              `(:use ((:instance aignet-mark-const-nodes-class-contra-correct
                       (constmarks ,(acl2::hq orig-constmarks))
                       (litclasses ,(acl2::hq orig-litclasses))
                       (lit ,(acl2::hq lit))))
                :in-theory (disable aignet-mark-const-nodes-class-contra-correct)))
             (:pass1
              `(:use ((:instance aignet-mark-const-nodes-fixpoint-contra-correct
                       (constmarks ,(acl2::hq constmarks))
                       (litclasses ,(acl2::hq litclasses))
                       (limit 10)))
                :in-theory (disable aignet-mark-const-nodes-fixpoint-contra-correct)))))
    :otf-flg t)

  (defret <fn>-of-aignet-lit-fix
    (equal (let ((lit (aignet-lit-fix lit aignet))) <call>)
           <call>)))


(define aignet-mark-const-nodes-top-list ((lits lit-listp)
                                     aignet
                                     constmarks
                                     litclasses)
  :guard (and (non-exec (equal constmarks (acl2::create-bitarr)))
              (non-exec (equal litclasses (create-litarr)))
              (aignet-lit-listp lits aignet))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp
                                          lits-max-id-val-when-aignet-lit-listp))))
  :returns (mv contra new-constmarks new-litclasses)
  :prepwork ((local (defthmd lits-max-id-val-when-aignet-lit-listp
                      (implies (aignet-lit-listp x aignet)
                               (< (lits-max-id-val x) (+ 1 (fanin-count aignet))))
                      :hints(("Goal" :in-theory (enable aignet-lit-listp
                                                        aignet-idp
                                                        lits-max-id-val)))
                      :rule-classes :forward-chaining)))
  (b* ((constmarks (mbe :logic (non-exec (acl2::create-bitarr)) :exec constmarks))
       (constmarks (resize-bits (num-fanins aignet) constmarks))
       (litclasses (mbe :logic (non-exec (create-litarr)) :exec litclasses))
       (litclasses (resize-lits (num-fanins aignet) litclasses))
       ((acl2::hintcontext-bind ((orig-constmarks constmarks)
                                 (orig-litclasses litclasses))))
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-class-list lits aignet constmarks litclasses))
       ((when contra)
        (acl2::hintcontext
         :contra
         (mv contra constmarks litclasses)))
       ((acl2::hintcontext :pass1)))
    (aignet-mark-const-nodes-fixpoint 10 aignet constmarks litclasses))
  ///

  (defret norm-<fn>
    (implies (syntaxp (not (and (equal constmarks ''nil)
                                (equal litclasses ''nil))))
             (equal <call>
                    (let ((constmarks nil) (litclasses nil)) <call>))))

  (defret litclasses-orderedp-of-<fn>
    (litclasses-orderedp new-litclasses))

  (defret litclasses-size-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (len new-litclasses)
                    (num-fanins aignet)))
    :hints(("Goal" :in-theory (enable aignet-idp
                                      lits-max-id-val-when-aignet-lit-listp))))

  (defret constmarks-size-of-<fn>
    (implies (aignet-lit-listp lits aignet)
             (equal (len new-constmarks)
                    (num-fanins aignet)))
    :hints(("Goal" :in-theory (enable aignet-idp
                                      lits-max-id-val-when-aignet-lit-listp))))

  (defret litclasses-invar-of-<fn>
    (implies (and (equal (aignet-eval-conjunction lits invals regvals aignet) 1)
                  (aignet-lit-listp lits aignet))
             (litclasses-invar invals regvals new-constmarks new-litclasses aignet)))

  (set-ignore-ok t)

  (defret <fn>-contra-correct
    (implies (and (equal (aignet-eval-conjunction lits invals regvals aignet) 1)
                  (aignet-lit-listp lits aignet))
             (not contra))
    :hints (("goal" :do-not-induct t)
            (acl2::function-termhint
             aignet-mark-const-nodes-top-list
             (:contra
              `(:use ((:instance aignet-mark-const-nodes-class-list-contra-correct
                       (constmarks ,(acl2::hq orig-constmarks))
                       (litclasses ,(acl2::hq orig-litclasses))
                       (lits ,(acl2::hq lits))))
                :in-theory (disable aignet-mark-const-nodes-class-list-contra-correct)))
             (:pass1
              `(:use ((:instance aignet-mark-const-nodes-fixpoint-contra-correct
                       (constmarks ,(acl2::hq constmarks))
                       (litclasses ,(acl2::hq litclasses))
                       (limit 10)))
                :in-theory (disable aignet-mark-const-nodes-fixpoint-contra-correct)))))
    :otf-flg t))


;; (define aignet-self-constprop-init-litclass-pis ((n natp :type (integer 0 *))
;;                                                  constmarks
;;                                                  litclasses
;;                                                  aignet)
;;   :guard (and (<= n (num-ins aignet))
;;               (ec-call (litclasses-orderedp litclasses))
;;               (<= (num-fanins aignet) (bits-length constmarks))
;;               (<= (num-fanins aignet) (lits-length litclasses)))
;;   :returns (mv new-litclasses new-constmarks)
;;   :verify-guards nil
;;   :measure (nfix (- (num-ins aignet) (nfix n)))
;;   (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
;;                    :exec (int= n (num-ins aignet))))
;;         litclasses)
;;        (id (innum->id n aignet))
;;        (norm-lit (id-normal-form id constmarks litclasses))
;;        (litclasses (set-lit id norm-lit litclasses)))
;;     (aignet-self-constprop-init-litclass-pis (1+ (lnfix n)) constmarks litclasses aignet))
;;   ///
;;   (local (in-theory (disable (:d aignet-self-constprop-init-litclass-pis))))

;;   (defret litclasses-invar-preserved-by-<fn>
;;     (implies (litclasses-invar invals regvals constmarks litclasses aignet)
;;              (litclasses-invar invals regvals new-constmarks new-litclasses aignet))
;;     :hints (("goal" :induct <call>
;;              :expand (<call>))
;;             (and stable-under-simplificationp
;;                  (let ((lit (assoc 'litclasses-invar clause)))
;;                    `(:expand (,lit
;;                               (:free (constmarks litclasses)
;;                                (id-eval (litclasses-invar-witness
;;                                          invals regvals constmarks litclasses aignet)
;;                                         invals regvals aignet))))))))

;;   (defret litclasses-orderedp-preserved-by-<fn>
;;     (implies (litclasses-orderedp litclasses)
;;              (litclasses-orderedp new-litclasses))
;;     :hints (("goal" :induct <call>
;;              :expand (<call>))
;;             (and stable-under-simplificationp
;;                  (let ((lit (assoc 'litclasses-orderedp clause)))
;;                    `(:expand (,lit))))))

;;   (verify-guards aignet-self-constprop-init-litclass-pis))


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




(defsection self-constprop-dfs-invar
  (defun-sk self-constprop-dfs-invar (invals regvals aignet mark copy)
    (forall id
            (implies (equal 1 (get-bit id mark))
                     (equal (lit-eval (nth-lit id copy) invals regvals aignet)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable self-constprop-dfs-invar))

  (defthm self-constprop-dfs-invar-implies-lit-eval-lit-copy
    (implies (and (self-constprop-dfs-invar invals regvals aignet mark copy)
                  (equal 1 (nth (lit->var lit) mark)))
             (equal (lit-eval (lit-copy lit copy) invals regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-copy)
            :expand ((lit-eval lit invals regvals aignet)))))

  (defthm self-constprop-dfs-invar-of-node-list-fix
    (iff (self-constprop-dfs-invar invals regvals (node-list-fix aignet) mark copy)
         (self-constprop-dfs-invar invals regvals aignet mark copy))
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'self-constprop-dfs-invar clause)))
                   `(:expand (,lit)
                     :use ((:instance self-constprop-dfs-invar-necc
                            (aignet (node-list-fix aignet))
                            (id (self-constprop-dfs-invar-witness . ,(cdr lit))))
                           (:instance self-constprop-dfs-invar-necc
                            (aignet aignet)
                            (id (self-constprop-dfs-invar-witness . ,(cdr lit)))))
                     :in-theory (disable self-constprop-dfs-invar-necc)))))))

(defsection self-constprop-ci-invar
  (local (in-theory (disable lookup-id-out-of-bounds)))

  (defun-sk self-constprop-ci-invar (invals regvals aignet copy)
    (forall id
            (implies (equal (ctype (stype (car (lookup-id id aignet)))) :input)
                     (equal (lit-eval (nth-lit id copy) invals regvals aignet)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable self-constprop-ci-invar))

  (defthm self-constprop-ci-invar-implies-lit-eval-lit-copy
    (implies (and (self-constprop-ci-invar invals regvals aignet copy)
                  (equal (ctype (stype (car (lookup-id (lit->var lit) aignet)))) :input))
             (equal (lit-eval (lit-copy lit copy) invals regvals aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-copy)
            :expand ((lit-eval lit invals regvals aignet)))))

  (defthm aignet-copy-dfs-rec-does-not-update-input-copies
    (b* (((mv ?new-mark new-copy ?new-strash ?new-aignet)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
      (implies (equal (ctype (stype (car (lookup-id k aignet)))) :input)
               (equal (nth-lit k new-copy)
                      (nth-lit k copy))))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-rec))))

  (local (defthm not-equal-stype-when-new
           (implies (and (aignet-extension-binding)
                         (not (aignet-idp id orig))
                         (equal (stype-count stype orig)
                                (stype-count stype new))
                         (not (equal stype :const)))
                    (not (equal (stype (car (lookup-id id new))) stype)))
           :hints(("Goal" :in-theory (e/d (;; lookup-id
                                           aignet-idp ;; fanin-count aignet-extension-p
                                           (:i aignet-extension-p))
                                          (lookup-id-out-of-bounds
                                           lookup-id-in-extension-inverse))
                   :induct (aignet-extension-p new orig)
                   :expand ((lookup-id id new)
                            (fanin-count new)
                            (aignet-extension-p new orig))))))

  (local (defthm ctype-equal-input-in-extension
           (implies (and (aignet-extension-binding)
                         (not (aignet-idp id orig))
                         (equal (stype-count :pi orig)
                                (stype-count :pi new))
                         (equal (stype-count :reg orig)
                                (stype-count :reg new)))
                    (not (equal (ctype (stype (car (lookup-id id new)))) :input)))
           :hints(("Goal" :in-theory (enable ctype)))))

  (defthm aignet-copy-dfs-rec-preserves-self-constprop-ci-invar
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
      (implies (and (self-constprop-ci-invar invals regvals aignet copy)
                    (aignet-input-copies-in-bounds copy aignet aignet))
               (self-constprop-ci-invar invals regvals new-aignet new-copy)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (disable LOOKUP-ID-IMPLIES-AIGNET-IDP)
                   :cases ((aignet-idp (self-constprop-ci-invar-witness . ,(cdar (last clause))) aignet))))))

  (local (defthm ctype-when-not-const-or-gate
           (b* ((stype (stype (car (lookup-id id aignet)))))
             (implies (and (not (equal stype :const))
                           (not (equal (ctype stype) :gate)))
                      (equal (ctype stype) :input)))
           :hints(("Goal" :in-theory (enable ctype)))))

  (defthmd bit-equiv-congruence-of-equal-1
    (implies (bit-equiv a b)
             (equal (equal 1 a) (equal 1 b)))
    :rule-classes :congruence)

  (local (defthm aignet-idp-by-marks-boundedp
           (implies (and (equal 1 (nth id mark))
                         (marks-boundedp (+ 1 (fanin-count aignet)) mark))
                    (aignet-idp id aignet))
           :hints(("Goal" :in-theory (enable aignet-idp
                                             lookup-when-marks-boundedp
                                             bit-equiv-congruence-of-equal-1)))))

  (local (defthm lit-eval-when-lit-copy-equal-0
           ;; (b* ((copy (mv-nth 1 dfs))
           ;;      (mark (mv-nth 0 dfs))
           ;;      (aignet (mv-nth 3 dfs)))
           (implies (and (equal (lit-copy lit copy) 0)
                         (self-constprop-dfs-invar invals regvals new-aignet mark copy)
                         (aignet-extension-p new-aignet aignet)
                         (aignet-litp lit aignet)
                         (equal 1 (nth (lit->var lit) mark)))
                    (equal (lit-eval lit invals regvals aignet)
                           0))
           :hints (("goal" :use ((:instance self-constprop-dfs-invar-implies-lit-eval-lit-copy
                                  (aignet new-aignet)))
                    :in-theory (disable self-constprop-dfs-invar-implies-lit-eval-lit-copy)))))
                         ;; (equal (lit-eval (lit-copy lit copy) invals regvals new-aignet)
                         ;;        (lit-eval lit invals regvals aignet))

  (defthm aignet-copy-dfs-rec-preserves-self-constprop-dfs-invar
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
      (implies (and (self-constprop-ci-invar invals regvals aignet copy)
                    (self-constprop-dfs-invar invals regvals aignet mark copy)
                    (aignet-input-copies-in-bounds copy aignet aignet)
                    (aignet-marked-copies-in-bounds copy mark aignet)
                    (marks-boundedp (num-fanins aignet) mark))
               (self-constprop-dfs-invar invals regvals new-aignet new-mark new-copy)))
    :hints(("Goal" :in-theory (enable (:i aignet-self-copy-dfs-rec))
            :induct (aignet-self-copy-dfs-rec id aignet mark copy strash gatesimp)
            :expand ((aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))
                  :do-not-induct t))
           (and stable-under-simplificationp
                '(:expand ((id-eval id invals regvals aignet))
                  :in-theory (enable* eval-xor-of-lits
                                      eval-and-of-lits
                                      acl2::arith-equiv-forwarding)))))


  

  (defthm self-constprop-ci-invar-of-node-list-fix
    (iff (self-constprop-ci-invar invals regvals (node-list-fix aignet) copy)
         (self-constprop-ci-invar invals regvals aignet copy))
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'self-constprop-ci-invar clause)))
                   `(:expand (,lit)
                     :use ((:instance self-constprop-ci-invar-necc
                            (aignet (node-list-fix aignet))
                            (id (self-constprop-ci-invar-witness . ,(cdr lit))))
                           (:instance self-constprop-ci-invar-necc
                            (aignet aignet)
                            (id (self-constprop-ci-invar-witness . ,(cdr lit)))))
                     :in-theory (disable self-constprop-ci-invar-necc)))))))





(define aignet-self-constprop-copy-init ((n natp :type (integer 0 *))
                                         constmarks
                                         litclasses
                                         aignet
                                         copy)
  :guard (and (<= n (num-fanins aignet))
              (ec-call (litclasses-orderedp litclasses))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (<= (num-fanins aignet) (lits-length copy)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :returns (new-copy)
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        copy)
       ((unless (or (eql 1 (get-bit n constmarks))
                    (eql (id->type n aignet) (in-type))))
        (aignet-self-constprop-copy-init (1+ (lnfix n)) constmarks litclasses aignet copy))
       (norm-lit (id-normal-form n constmarks litclasses))
       (copy (set-lit n norm-lit copy)))
    (aignet-self-constprop-copy-init (1+ (lnfix n)) constmarks litclasses aignet copy))
  ///
  (local (in-theory (enable* acl2::arith-equiv-forwarding)))

  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (or (equal (id->type k aignet) (in-type))
                        (equal 1 (nth k constmarks)))
                    (<= (nfix n) (nfix k))
                    (< (nfix k) (num-fanins aignet)))
               (id-normal-form k constmarks litclasses)
             (nth-lit k copy))))

  (defret len-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))



  ;; (local (defthm aignet-idp-by-marks-boundedp
  ;;          (implies (and (equal 1 (nth id mark))
  ;;                        (marks-boundedp (+ 1 (fanin-count aignet)) mark))
  ;;                   (aignet-idp id aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-idp
  ;;                                            lookup-when-marks-boundedp
  ;;                                            bit-equiv-congruence-of-equal-1)))))


  (defthm self-constprop-dfs-invar-of-<fn>
    (b* ((new-copy (aignet-self-constprop-copy-init 0 constmarks litclasses aignet copy)))
      (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                    (marks-boundedp (num-fanins aignet) constmarks))
               (self-constprop-dfs-invar invals regvals aignet constmarks new-copy)))
    :hints(("Goal" :in-theory (e/d (self-constprop-dfs-invar
                                    lookup-when-marks-boundedp
                                    bit-equiv-congruence-of-equal-1
                                    aignet-idp)))))

  (defthm self-constprop-ci-invar-of-<fn>
    (b* ((new-copy (aignet-self-constprop-copy-init 0 constmarks litclasses aignet copy)))
      (implies (litclasses-invar invals regvals constmarks litclasses aignet)
               (self-constprop-ci-invar invals regvals aignet new-copy)))
    :hints(("Goal" :in-theory (enable self-constprop-ci-invar))))

  (defret aignet-input-copies-in-bounds-of-<fn>
    :pre-bind ((n 0))
    (aignet-input-copies-in-bounds new-copy aignet aignet)
    :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds
                                      aignet-idp))))

  (defret aignet-marked-copies-in-bounds-of-<fn>
    :pre-bind ((n 0))
    (implies (marks-boundedp (+ 1 (fanin-count aignet)) constmarks)
             (aignet-marked-copies-in-bounds new-copy constmarks aignet))
    :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds
                                      lookup-when-marks-boundedp
                                      aignet-idp
                                      bit-equiv-congruence-of-equal-1)))))

(define aignet-self-constprop-prep ((hyps lit-listp) aignet constmarks copy)
  :guard (and (aignet-lit-listp hyps aignet)
              (non-exec (equal copy (create-copy)))
              (non-exec (equal constmarks (create-constmarks))))
  :returns (mv (new-constmarks) (new-copy))
  :guard-debug t
  (b* (((acl2::local-stobjs litclasses)
        (mv constmarks copy litclasses))
       ((mv ?contra constmarks litclasses) (aignet-mark-const-nodes-top-list hyps aignet constmarks litclasses))
       (copy (mbe :logic (non-exec (create-copy))
                  :exec copy))
       (copy (resize-lits (num-fanins aignet) copy))
       (copy (aignet-self-constprop-copy-init 0 constmarks litclasses aignet copy)))
    (mv constmarks copy litclasses))
  ///

  (defret normalize-aignet-self-constprop-prep
    (implies (syntaxp (not (and (equal copy ''nil)
                                (equal constmarks ''nil))))
             (equal <call>
                    (let ((copy nil) (constmarks nil)) <call>))))

  (defret size-of-aignet-self-constprop-prep-copy
    (implies (aignet-lit-listp hyps aignet)
             (equal (len new-copy) (num-fanins aignet))))

  (defret size-of-aignet-self-constprop-prep-constmarks
    (implies (aignet-lit-listp hyps aignet)
             (equal (len new-constmarks) (num-fanins aignet))))

  (defret aignet-input-copies-in-bounds-of-<fn>
    (aignet-input-copies-in-bounds new-copy aignet aignet))

  (defret aignet-marked-copies-in-bounds-of-<fn>
    (implies (aignet-lit-listp hyps aignet)
             (aignet-marked-copies-in-bounds new-copy new-constmarks aignet)))

  (defret self-constprop-ci-invar-of-<fn>
    (implies (and (aignet-lit-listp hyps aignet)
                  (equal 1 (aignet-eval-conjunction hyps invals regvals aignet)))
             (self-constprop-ci-invar invals regvals aignet new-copy)))

  (defret self-constprop-dfs-invar-of-<fn>
    (implies (and (aignet-lit-listp hyps aignet)
                  (equal 1 (aignet-eval-conjunction hyps invals regvals aignet)))
             (self-constprop-dfs-invar invals regvals aignet new-constmarks new-copy))))




(defthmd lits-max-id-val-when-aignet-lit-listp
  (implies (aignet-lit-listp lits aignet)
           (<= (lits-max-id-val lits) (fanin-count aignet)))
  :hints(("Goal" :in-theory (enable aignet-lit-listp aignet-idp lits-max-id-val)))
  :rule-classes :forward-chaining)


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

  (defret mark-len-preserved-of-<fn>
    (implies (< (lits-max-id-val lits) (len mark))
             (equal (len new-mark)
                    (len mark)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret copy-len-preserved-of-<fn>
    (implies (< (lits-max-id-val lits) (len copy))
             (equal (len new-copy)
                    (len copy)))
    :hints ((acl2::just-induct-and-expand <call>)))

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
              (and (< (lit->var lit) (+ 1 (fanin-count aignet)))
                   (<= (lit->var lit) (fanin-count aignet))))
     :hints(("Goal" :in-theory (enable aignet-idp)))))

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
                  (marks-boundedp (+ 1 (fanin-count orig)) mark)
                  (equal (stype-count :pi new) (stype-count :pi orig))
                  (equal (stype-count :reg new) (stype-count :reg orig)))
             (iff (dfs-copy-onto-invar new mark copy aignet2)
                  (dfs-copy-onto-invar orig mark copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(assoc 'dfs-copy-onto-invar clause))
                   :in-theory (enable aignet-idp lookup-when-marks-boundedp-split)))))
             

  (defret dfs-copy-onto-invar-holds-of-<fn>
    (implies (and (aignet-lit-listp lits aignet)
                  (marks-boundedp (+ 1 (fanin-count aignet)) mark)
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
                          (limit (+ 1 (fanin-count aignet)))))
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
                  (marks-boundedp (+ 1 (fanin-count aignet)) mark)
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
                                 lit-eval-list-of-copies-when-dfs-copy-onto-invar))))

  (defret aignet-self-copy-dfs-rec-list-preserves-marks-boundedp
    (implies (and (marks-boundedp limit mark)
                  (< (lits-max-id-val lits) (nfix limit)))
             (marks-boundedp limit new-mark))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-self-copy-dfs-rec-list-preserves-self-constprop-ci-invar
    (implies (and (self-constprop-ci-invar invals regvals aignet copy)
                  (aignet-input-copies-in-bounds copy aignet aignet))
             (self-constprop-ci-invar invals regvals new-aignet new-copy))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (in-theory (enable lits-max-id-val-when-aignet-lit-listp)))

  (defret aignet-self-copy-dfs-rec-list-preserves-self-constprop-dfs-invar
    (implies (and (self-constprop-ci-invar invals regvals aignet copy)
                  (self-constprop-dfs-invar invals regvals aignet mark copy)
                  (aignet-input-copies-in-bounds copy aignet aignet)
                  (aignet-marked-copies-in-bounds copy mark aignet)
                  (marks-boundedp (num-fanins aignet) mark)
                  (aignet-lit-listp lits aignet))
             (self-constprop-dfs-invar invals regvals new-aignet new-mark new-copy))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-lit-listp-of-lit-list-copies-of-<fn>
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet))
             (aignet-lit-listp (lit-list-copies lits new-copy) new-aignet))
    :hints (("goal" :use ((:instance aignet-marked-copies-in-bounds-of-aignet-self-copy-dfs-rec-list))
             :in-theory (disable aignet-marked-copies-in-bounds-of-aignet-self-copy-dfs-rec-list)))))

(define self-constprop-invar (invals regvals aignet mark copy)
  :verify-guards nil
  (and (self-constprop-ci-invar invals regvals aignet copy)
       (self-constprop-dfs-invar invals regvals aignet mark copy)
       (aignet-input-copies-in-bounds copy aignet aignet)
       (aignet-marked-copies-in-bounds copy mark aignet)
       (marks-boundedp (num-fanins aignet) mark))
  ///
  (defthm aignet-copy-dfs-rec-preserves-self-constprop-invar
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
      (implies (and (self-constprop-invar invals regvals aignet mark copy)
                    (aignet-idp id aignet))
               (self-constprop-invar invals regvals new-aignet new-mark new-copy)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-self-copy-dfs-rec-list-preserves-self-constprop-invar
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-self-copy-dfs-rec-list lits aignet mark copy strash gatesimp)))
      (implies (and (self-constprop-invar invals regvals aignet mark copy)
                    (aignet-lit-listp lits aignet))
               (self-constprop-invar invals regvals new-aignet new-mark new-copy)))
    :hints(("Goal" :in-theory (enable lits-max-id-val-when-aignet-lit-listp))))

  (defthm self-constprop-invar-of-aignet-self-constprop-prep
    (implies (and (aignet-lit-listp hyps aignet)
                  (equal 1 (aignet-eval-conjunction hyps invals regvals aignet)))
             (b* (((mv constmarks copy)
                   (aignet-self-constprop-prep hyps aignet constmarks copy)))
               (self-constprop-invar invals regvals aignet constmarks copy)))))

(define self-constprop-guard (aignet mark copy)
  (and ;; (<= (lnfix bound) (bits-length mark))
   ;; (<= (lnfix bound) (lits-length copy))
   (equal (bits-length mark) (lits-length copy))
   (<= (bits-length mark) (num-fanins aignet))
   ;; (<= (bits-length mark) (num-fanins aignet))
   ;; (<= (lits-length copy) (num-fanins aignet))
   (ec-call (aignet-marked-copies-in-bounds copy mark aignet))
   (ec-call (aignet-input-copies-in-bounds copy aignet aignet)))
  ///
  (defthm aignet-copy-dfs-rec-preserves-self-constprop-guard
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
      (implies (and (self-constprop-guard aignet mark copy)
                    (< (nfix id) (len mark)))
               (self-constprop-guard new-aignet new-mark new-copy))))

  (defthm aignet-copy-dfs-rec-list-preserves-self-constprop-guard
    (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
          (aignet-self-copy-dfs-rec-list lits aignet mark copy strash gatesimp)))
      (implies (and (self-constprop-guard aignet mark copy)
                    (< (lits-max-id-val lits) (len mark)))
               (self-constprop-guard new-aignet new-mark new-copy))))

  (defthm self-constprop-guard-of-aignet-self-constprop-prep
    (implies (aignet-lit-listp hyps aignet)
             (b* (((mv constmarks copy)
                   (aignet-self-constprop-prep hyps aignet constmarks copy)))
               (self-constprop-guard aignet constmarks copy))))

  (defthm self-constprop-guard-implies-copy-len
    (implies (self-constprop-guard aignet mark copy)
             (equal (len copy) (len mark)))
    :rule-classes :forward-chaining)

  (defthm self-constprop-guard-implies-copies-in-bounds
    (implies (self-constprop-guard aignet mark copy)
             (and (aignet-marked-copies-in-bounds copy mark aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet))))

  ;; (defthm self-constprop-guard-of-lesser-bound
  ;;   (implies (and (self-constprop-guard bound1 aignet mark copy)
  ;;                 (<= (nfix bound) (nfix bound1)))
  ;;            (self-constprop-guard aignet mark copy)))

  ;; (defthm self-constprop-guard-of-aignet-extension
  ;;   (implies (and (aignet-extension-binding)
  ;;                 (self-constprop-guard orig mark copy)
  ;;                 (equal (stype-count :pi new) (stype-count :pi orig))
  ;;                 (equal (stype-count :reg new) (stype-count :reg orig)))
  ;;            (self-constprop-guard new mark copy)))
  )



(define aignet-self-constprop-init-pis ((n natp :type (integer 0 *))
                                        constmarks
                                        litclasses
                                        aignet
                                        copy)
  :guard (and (<= n (num-ins aignet))
              (ec-call (litclasses-orderedp litclasses))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (<= (num-fanins aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (int= n (num-ins aignet))))
        copy)
       (id (innum->id n aignet))
       (norm-lit (id-normal-form id constmarks litclasses))
       (copy (set-lit id norm-lit copy)))
    (aignet-self-constprop-init-pis (1+ (lnfix n)) constmarks litclasses aignet copy))
  ///
  (local (in-theory (disable (:d aignet-self-constprop-init-pis))))

  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 0)
                    (<= (nfix n) (ci-id->ionum k aignet)))
               (id-normal-form k constmarks litclasses)
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (verify-guards aignet-self-constprop-init-pis))

(define aignet-self-constprop-init-regs ((n natp :type (integer 0 *))
                                        constmarks
                                        litclasses
                                        aignet
                                        copy)
  :guard (and (<= n (num-regs aignet))
              (ec-call (litclasses-orderedp litclasses))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (<= (num-fanins aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (int= n (num-regs aignet))))
        copy)
       (id (regnum->id n aignet))
       (norm-lit (id-normal-form id constmarks litclasses))
       (copy (set-lit id norm-lit copy)))
    (aignet-self-constprop-init-regs (1+ (lnfix n)) constmarks litclasses aignet copy))
  ///
  (local (in-theory (disable (:d aignet-self-constprop-init-regs))))

  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 1)
                    (<= (nfix n) (ci-id->ionum k aignet)))
               (id-normal-form k constmarks litclasses)
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (verify-guards aignet-self-constprop-init-regs))


(defthm aignet-input-copies-in-bounds-of-self-constprop-init
  (b* ((copy (aignet-self-constprop-init-pis 0 constmarks vals aignet copy))
       (copy (aignet-self-constprop-init-regs 0 constmarks vals aignet copy)))
    (aignet-input-copies-in-bounds copy aignet aignet))
  :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds
                                    aignet-idp))))

(defthm aignet-marked-copies-in-bounds-of-resize-empty
  (aignet-marked-copies-in-bounds copy (resize-list nil n 0) aignet)
  :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds))))

(defthm dfs-copy-onto-invar-of-resize-empty
  (dfs-copy-onto-invar  aignet (resize-list nil n 0) copy aignet2)
  :hints(("Goal" :in-theory (enable dfs-copy-onto-invar))))


;; (defsection marked-nodes-invar
;;   (defun-sk marked-nodes-invar (mark vals invals regvals aignet)
;;     (forall id
;;             (implies (and (equal (id->type id aignet) (in-type))
;;                           (equal (get-bit id mark) 1))
;;                      (equal (id-eval id invals regvals aignet)
;;                             (get-bit id vals))))
;;     :rewrite :direct)

;;   (in-theory (disable marked-nodes-invar))

;;   (defthm aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
;;     (implies (and (equal (lit-eval lit invals regvals aignet) 1)
;;                   (marked-nodes-invar mark vals invals regvals aignet))
;;              (b* (((mv new-mark new-vals) (aignet-mark-const-nodes-rec lit aignet mark vals)))
;;                (marked-nodes-invar new-mark new-vals invals regvals aignet)))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))
;;             (and stable-under-simplificationp
;;                  (let ((witness (acl2::find-call-lst
;;                                  'marked-nodes-invar-witness
;;                                  clause)))
;;                    `(:clause-processor
;;                      (acl2::simple-generalize-cp
;;                       clause '((,witness . witness))))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((equal 1 (get-bit witness mark)))))))

;;   (defthm marked-nodes-invar-of-empty-mark
;;     (marked-nodes-invar (resize-list nil k 0) vals invals regvals aignet)
;;     :hints(("Goal" :in-theory (enable marked-nodes-invar)))))

;; (in-theory (disable marked-nodes-invar-necc))
;; (local (in-theory (enable marked-nodes-invar-necc)))



;; (defsection constprop-marked-pis-true
;;   (defun-sk constprop-marked-pis-true (n
;;                                        constmarks
;;                                        vals
;;                                        aignet
;;                                        invals
;;                                        regvals)
;;     (forall id
;;             (implies (and (equal (id->type id aignet) (in-type))
;;                           (equal (id->regp id aignet) 0)
;;                           (<= (nfix n) (ci-id->ionum id aignet))
;;                           (equal (get-bit id constmarks) 1))
;;                      (equal (id-eval id invals regvals aignet)
;;                             (get-bit id vals))))
;;     :rewrite :direct)

;;   (in-theory (disable constprop-marked-pis-true))

;;   (local (in-theory (disable id-eval-of-input-index)))

;;   (defthm constprop-marked-pis-true-when-true-for-one-greater
;;     (implies (and (constprop-marked-pis-true (+ 1 (nfix n)) constmarks vals aignet invals regvals)
;;                   (let ((id (innum->id n aignet)))
;;                     (implies (and (equal (id->type id aignet) (in-type))
;;                                   (equal (id->regp id aignet) 0)
;;                                   (<= (nfix n) (ci-id->ionum id aignet))
;;                                   (equal (get-bit id constmarks) 1))
;;                              (equal (id-eval id invals regvals aignet)
;;                                     (get-bit id vals)))))
;;              (constprop-marked-pis-true n constmarks vals aignet invals regvals))
;;     :hints (("goal" :in-theory (enable* arith-equiv-forwarding))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))
;;             (and stable-under-simplificationp
;;                  (let ((witness (acl2::find-call-lst
;;                                  'constprop-marked-pis-true-witness
;;                                  clause)))
;;                    `(:clause-processor
;;                      (acl2::simple-generalize-cp
;;                       clause '((,witness . witness))))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((nat-equiv n (ci-id->ionum witness aignet))))))
;;     :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;;   (defthm constprop-marked-pis-true-end
;;     (implies (<= (num-ins aignet) (nfix n))
;;              (constprop-marked-pis-true n constmarks vals aignet invals regvals))
;;     :hints(("Goal" :in-theory (enable constprop-marked-pis-true))))


;;   (defthm constprop-marked-pis-true-implies-one-greater
;;     (implies (constprop-marked-pis-true n constmarks vals aignet invals regvals)
;;              (constprop-marked-pis-true (+ 1 (nfix n)) constmarks vals aignet invals regvals))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

  
;;   (defthm constprop-marked-pis-true-implies-nth-invals
;;     (implies (and (constprop-marked-pis-true n constmarks vals aignet invals regvals)
;;                   (<= (nfix n) (nfix k))
;;                   (< (nfix k) (num-ins aignet))
;;                   (equal (nth (innum->id k aignet) constmarks) 1))
;;              (bit-equiv (nth k invals)
;;                         (get-bit (innum->id k aignet) vals)))
;;     :hints (("goal" :use ((:instance constprop-marked-pis-true-necc
;;                            (id (innum->id k aignet))))
;;              :in-theory (e/d (id-eval-of-input-index)
;;                              (constprop-marked-pis-true-necc)))))

;;   (defthm constprop-marked-pis-true-of-mark-const-nodes
;;     (implies (and (constprop-marked-pis-true 0 constmarks vals aignet invals regvals)
;;                   (marked-nodes-invar constmarks vals invals regvals aignet)
;;                   (equal (lit-eval lit invals regvals aignet) 1))
;;              (b* (((mv new-constmarks new-vals)
;;                    (aignet-mark-const-nodes-rec lit aignet constmarks vals)))
;;                (constprop-marked-pis-true 0 new-constmarks new-vals aignet invals regvals)))
;;     :hints (("goal" :use ((:instance aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
;;                            (mark constmarks)))
;;              :in-theory (disable aignet-mark-const-nodes-rec-preserves-marked-nodes-invar))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (defthm constprop-marked-pis-true-of-empty-constmarks
;;     (constprop-marked-pis-true n (resize-list nil k 0) vals aignet invals regvals)
;;     :hints(("Goal" :in-theory (enable constprop-marked-pis-true)))))

;; (defsection constprop-marked-regs-true
;;   (defun-sk constprop-marked-regs-true (n
;;                                        constmarks
;;                                        vals
;;                                        aignet
;;                                        invals
;;                                        regvals)
;;     (forall id
;;             (implies (and (equal (id->type id aignet) (in-type))
;;                           (equal (id->regp id aignet) 1)
;;                           (<= (nfix n) (ci-id->ionum id aignet))
;;                           (equal (get-bit id constmarks) 1))
;;                      (equal (id-eval id invals regvals aignet)
;;                             (get-bit id vals))))
;;     :rewrite :direct)

;;   (in-theory (disable constprop-marked-regs-true))

;;   (local (in-theory (disable id-eval-of-reg-index)))

;;   (defthm constprop-marked-regs-true-when-true-for-one-greater
;;     (implies (and (constprop-marked-regs-true (+ 1 (nfix n)) constmarks vals aignet invals regvals)
;;                   (let ((id (regnum->id n aignet)))
;;                     (implies (and (equal (id->type id aignet) (in-type))
;;                                   (equal (id->regp id aignet) 1)
;;                                   (<= (nfix n) (ci-id->ionum id aignet))
;;                                   (equal (get-bit id constmarks) 1))
;;                              (equal (id-eval id invals regvals aignet)
;;                                     (get-bit id vals)))))
;;              (constprop-marked-regs-true n constmarks vals aignet invals regvals))
;;     :hints (("goal" :in-theory (enable* arith-equiv-forwarding))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))
;;             (and stable-under-simplificationp
;;                  (let ((witness (acl2::find-call-lst
;;                                  'constprop-marked-regs-true-witness
;;                                  clause)))
;;                    `(:clause-processor
;;                      (acl2::simple-generalize-cp
;;                       clause '((,witness . witness))))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((nat-equiv n (ci-id->ionum witness aignet))))))
;;     :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))


;;   (defthm constprop-marked-regs-true-end
;;     (implies (<= (num-regs aignet) (nfix n))
;;              (constprop-marked-regs-true n constmarks vals aignet invals regvals))
;;     :hints(("Goal" :in-theory (enable constprop-marked-regs-true))))


;;   (defthm constprop-marked-regs-true-implies-one-greater
;;     (implies (constprop-marked-regs-true n constmarks vals aignet invals regvals)
;;              (constprop-marked-regs-true (+ 1 (nfix n)) constmarks vals aignet invals regvals))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

  
;;   (defthm constprop-marked-regs-true-implies-nth-regvals
;;     (implies (and (constprop-marked-regs-true n constmarks vals aignet invals regvals)
;;                   (<= (nfix n) (nfix k))
;;                   (< (nfix k) (num-regs aignet))
;;                   (equal (nth (regnum->id k aignet) constmarks) 1))
;;              (bit-equiv (nth k regvals)
;;                         (get-bit (regnum->id k aignet) vals)))
;;     :hints (("goal" :use ((:instance constprop-marked-regs-true-necc
;;                            (id (regnum->id k aignet))))
;;              :in-theory (e/d (id-eval-of-reg-index)
;;                              (constprop-marked-regs-true-necc)))))

;;   (defthm constprop-marked-regs-true-of-mark-const-nodes
;;     (implies (and (constprop-marked-regs-true 0 constmarks vals aignet invals regvals)
;;                   (marked-nodes-invar constmarks vals invals regvals aignet)
;;                   (equal (lit-eval lit invals regvals aignet) 1))
;;              (b* (((mv new-constmarks new-vals)
;;                    (aignet-mark-const-nodes-rec lit aignet constmarks vals)))
;;                (constprop-marked-regs-true 0 new-constmarks new-vals aignet invals regvals)))
;;     :hints (("goal" :use ((:instance aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
;;                            (mark constmarks)))
;;              :in-theory (disable aignet-mark-const-nodes-rec-preserves-marked-nodes-invar))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (defthm constprop-marked-regs-true-of-empty-constmarks
;;     (constprop-marked-regs-true n (resize-list nil k 0) vals aignet invals regvals)
;;     :hints(("Goal" :in-theory (enable constprop-marked-regs-true)))))

















(local (in-theory (enable aignet-idp)))

(define aignet-parametrize-copyarr ((hyp litp) aignet copy)
  :guard (and (fanin-litp hyp aignet)
              (non-exec (equal copy (create-copy))))
  :returns (new-copy)
  :guard-debug t
  (b* (((acl2::local-stobjs constmarks litclasses)
        (mv copy constmarks litclasses))
       ((mv ?contra constmarks litclasses) (aignet-mark-const-nodes-top hyp aignet constmarks litclasses))
       (copy (mbe :logic (non-exec (create-copy))
                  :exec copy))
       (copy (resize-lits (num-fanins aignet) copy))
       (copy (aignet-self-constprop-init-pis 0 constmarks litclasses aignet copy))
       (copy (aignet-self-constprop-init-regs 0 constmarks litclasses aignet copy)))
    (mv copy constmarks litclasses))
  ///

  (defret normalize-aignet-parametrize-copyarr
    (implies (syntaxp (not (equal copy ''nil)))
             (equal new-copy
                    (let ((copy nil)) <call>))))

  (defret size-of-aignet-parametrize-copyarr
    (equal (len new-copy) (num-fanins aignet)))

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
       (implies (litclasses-invar invals regvals constmarks litclasses aignet)
                (bits-equiv (input-copy-values 0 invals regvals aignet
                                               (aignet-self-constprop-init-pis 0 constmarks litclasses aignet copy)
                                               aignet)
                            (take (num-ins aignet) invals)))
       :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))))

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
       (implies (litclasses-invar invals regvals constmarks litclasses aignet)
                (bits-equiv (reg-copy-values 0 invals regvals aignet
                                             (aignet-self-constprop-init-regs 0 constmarks litclasses aignet copy)
                                             aignet)
                            (take (num-regs aignet) regvals)))
       :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))))
     ))

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


;; (define self-constprop-invar (hyp mark copy aignet)
;;   :non-executable t
;;   :prepwork ((defun-sk self-constprop-copies-ok (hyp copy aignet)
;;                (forall (invals regvals)
;;                        (implies (equal 1 (lit-eval hyp invals regvals aignet))
;;                                 (and (bits-equiv (input-copy-values 0 invals regvals aignet copy aignet)
;;                                                  (take (num-ins aignet) invals))
;;                                      (bits-equiv (reg-copy-values 0 invals regvals aignet copy aignet)
;;                                                  (take (num-regs aignet) regvals)))))
;;                :rewrite :direct)
;;              (in-theory (disable self-constprop-copies-ok)))
;;   :verify-guards nil
;;   :hooks nil
;;   (and (dfs-copy-onto-invar aignet mark copy aignet)
;;        (marks-boundedp (+ 1 (fanin-count aignet)) mark)
;;        (aignet-input-copies-in-bounds copy aignet aignet)
;;        (aignet-marked-copies-in-bounds copy mark aignet)
;;        (self-constprop-copies-ok hyp copy aignet))
;;   ///
;;   (defthm self-constprop-invar-preserved-by-aignet-copy-dfs-rec
;;     (implies (and (self-constprop-invar hyp mark copy aignet)
;;                   (aignet-litp hyp aignet)
;;                   (aignet-idp id aignet))
;;              (b* (((mv mark copy & aignet)
;;                    (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
;;                (self-constprop-invar hyp mark copy aignet)))
;;     :hints(("Goal" :in-theory (enable aignet-idp))
;;            (and stable-under-simplificationp
;;                 `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

;;   (defthm self-constprop-invar-preserved-by-aignet-self-copy-dfs-rec-list
;;     (implies (and (self-constprop-invar hyp mark copy aignet)
;;                   (aignet-litp hyp aignet)
;;                   (aignet-lit-listp lits aignet))
;;              (b* (((mv mark copy & aignet)
;;                    (aignet-self-copy-dfs-rec-list lits aignet mark copy strash gatesimp)))
;;                (self-constprop-invar hyp mark copy aignet)))
;;     :hints(("goal" :in-theory (enable lits-max-id-val-when-aignet-lit-listp))
;;            (and stable-under-simplificationp
;;                 `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

;;   (defthm self-constprop-invar-of-aignet-parametrize-copyarr
;;     (self-constprop-invar hyp (resize-list nil n 0)
;;                           (aignet-parametrize-copyarr hyp aignet copy)
;;                           aignet)
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

;;   (defthm marked-lit-copy-when-self-constprop-invar
;;     (implies (and (self-constprop-invar hyp mark copy aignet)
;;                   (equal 1 (lit-eval hyp invals regvals aignet))
;;                   (equal 1 (get-bit id mark)))
;;              (equal (lit-eval (nth-lit id copy) invals regvals aignet)
;;                     (id-eval id invals regvals aignet))))

;;   (defthm marked-lit-copies-when-self-constprop-invar
;;     (implies (and (self-constprop-invar hyp mark copy aignet)
;;                   (equal 1 (lit-eval hyp invals regvals aignet))
;;                   (lit-list-marked lits mark))
;;              (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet)
;;                     (lit-eval-list lits invals regvals aignet)))))



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
       (mark (resize-bits (num-fanins aignet) mark))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec (lit->var lit) aignet mark copy strash (default-gatesimp))))
    (mv (lit-copy lit copy) strash aignet copy mark))
  ///
  (defret aignet-litp-of-<fn>
    (aignet-litp new-lit new-aignet)
    :hints(("Goal" :in-theory (disable aignet-idp))))

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
    :hints (("goal" :expand ((lit-eval (aignet-lit-fix lit aignet) invals regvals aignet)
                             (lit-eval lit invals regvals aignet))
             :use ((:instance lit-eval-of-aignet-lit-fix (x lit)))
             :in-theory (e/d (lit-copy)
                             (lit-eval-of-aignet-lit-fix))))))





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
       (mark (resize-bits (num-fanins aignet) mark))
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
                  (mark (resize-bits (num-fanins aignet) mark))
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


       
                                  








  
