; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "aignet-base")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable nth update-nth sets::double-containment)))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(acl2::def2darr s61v
                :elt-type (signed-byte 61)
                :elt-typep (lambda (x) (signed-byte-p 61 x))
                :default-elt 0
                :elt-fix ifix
                :elt-guard (integerp x)
                :elt-okp (and (<= x (1- (expt 2 60)))
                              (<= (- (expt 2 60)) x)))

(defun s61v-sizedp (s61v aignet)
  (declare (xargs :stobjs (s61v aignet)
                  :guard-hints ('(:in-theory (enable memo-tablep
                                                     acl2::aignetp)))))
  (mbe :logic (non-exec (memo-tablep (cdr s61v) aignet))
       :exec (<= (num-nodes aignet) (s61v-nrows s61v))))

(defun s61v-id-in-bounds (id s61v)
  (declare (xargs :guard (idp id)
                  :stobjs s61v
                  :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  (mbe :logic (non-exec (id-in-bounds id (cdr s61v)))
       :exec (< (id-val id) (s61v-nrows s61v))))

(defun s61v-iterator-in-bounds (n s61v)
  (declare (xargs :guard (natp n)
                  :stobjs s61v
                  :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
  (mbe :logic (non-exec (iterator-in-bounds n (cdr s61v)))
       :exec (<= (nfix n) (s61v-nrows s61v))))

(definline s61v-id-get (id n s61v)
  (declare (xargs :stobjs s61v
                  :guard (and (idp id)
                              (s61v-id-in-bounds id s61v)
                              (natp n)
                              (< n (s61v-ncols s61v)))))
  (s61v-get2 (id-val id) n s61v))

(definline s61v-id-set (id n v s61v)
  (declare (xargs :stobjs s61v
                  :guard (and (idp id)
                              (s61v-id-in-bounds id s61v)
                              (natp n)
                              (< n (s61v-ncols s61v))
                              (integerp v))))
  (s61v-set2 (id-val id) n v s61v))

(defsection bit-extend
  (definlined bit-extend (bit)
    (declare (xargs :guard (acl2::bitp bit)
                    :guard-hints (("goal" :in-theory (enable acl2::bitp)))))
    (mbe :logic (if (equal bit 1) -1 0)
         :exec (- (the bit bit))))

  (local (in-theory (enable bit-extend)))

  (defthm logbitp-bit-extend
    (equal (acl2::bool->bit (logbitp x (bit-extend b)))
           (acl2::bfix b))
    :hints(("Goal" :in-theory (enable bit-extend acl2::bool->bit)))))

(local (in-theory (disable acl2::nth-with-large-index)))

(defsection vecsim-to-eval
  (local (in-theory (enable acl2::aignetp)))

  (defiteration vecsim-to-eval (slot bit s61v aignet-vals aignet)
    (declare (type (integer 0 *) slot)
             (type (integer 0 *) bit)
             (xargs :stobjs (s61v aignet-vals aignet)
                    :guard (and (s61v-sizedp s61v aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (< slot (s61v-ncols s61v)))))
    (b* ((nid (to-id n))
         (slotval (s61v-id-get nid slot s61v))
         (bitval (acl2::logbit bit slotval))
         (aignet-vals (set-id->bit nid bitval aignet-vals)))
      aignet-vals)
    :returns aignet-vals
    :index n
    :last (num-nodes aignet))

  (local (in-theory (enable vecsim-to-eval-iter)))

  (defthm lookup-in-vecsim-to-eval-iter
    (equal (nth m (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet))
           (if (<= (nfix n) (nfix m))
               (nth m aignet-vals)
             (acl2::logbit bit (s61v-id-get (to-id m) slot s61v)))))

  ;; (defthm vecsim-to-eval-iter-of-update-eval-prev
  ;;   (equal (vecsim-to-eval-iter n slot bit s61v
  ;;                          (update-nth *bitsi* (update-nth m val (nth *bitsi* aignet-vals))
  ;;                                      aignet-vals)
  ;;                          aignet)
  ;;          (let ((aignet-vals (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)))
  ;;            (if (< (nfix m) (nfix n))
  ;;                aignet-vals
  ;;              (update-nth *bitsi* (update-nth m val (nth *bitsi* aignet-vals))
  ;;                          aignet-vals))))
  ;;   :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)
  ;;            :expand ((:free (aignet-vals)
  ;;                      (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet))))))
  )


(defsection s61v-copy-lit
  (defiteration s61v-copy-lit (in-lit out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (litp in-lit)
                                (idp out-id)
                                (s61v-id-in-bounds out-id s61v)
                                (s61v-id-in-bounds (lit-id in-lit) s61v))
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (s61v-id-set out-id n
                 (logxor (bit-extend (lit-neg in-lit))
                         (s61v-id-get (lit-id in-lit) n s61v))
                 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-copy-lit-iter)))

  (defthm memo-tablep-s61v-copy-lit-iter
    (implies (memo-tablep (cdr s61v) aignet)
             (memo-tablep (cdr (s61v-copy-lit-iter n in-lit out-id s61v)) aignet))
    :hints(("Goal" :in-theory (enable memo-tablep))))

  (defthm car-s61v-copy-lit-iter
    (equal (car (s61v-copy-lit-iter n in-lit out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-copy-lit-iter
    (implies (< (id-val out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-copy-lit-iter n in-lit out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-copy-lit-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-copy-lit-iter m in-lit id
                                                              s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-copy-lit-iter
    (equal (nth slot (nth n (cdr (s61v-copy-lit-iter m in-lit id s61v))))
           (if (and (equal (nfix n) (id-val id))
                    (< (nfix slot) (nfix m)))
               (logxor (bit-extend (lit-neg in-lit))
                       (nth slot (nth (id-val (lit-id in-lit)) (cdr s61v))))
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-copy-lit-iter m in-lit id s61v))))


  (defthm vecsim-to-eval-of-s61v-copy-lit-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-copy-lit-iter slot1 in-lit m s61v) aignet-vals aignet)
           (let ((aignet-vals (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)))
             (if (and (< (id-val m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth (id-val m)
                             (acl2::b-xor (lit-neg in-lit)
                                          (acl2::logbit bit (nth
                                                             slot
                                                             (nth
                                                              (id-val
                                                               (lit-id
                                                                in-lit))
                                                              (cdr s61v)))))
                             aignet-vals)
               aignet-vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v
                                            aignet-vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v aignet-vals
                                            aignet)))))))

(defsection s61v-and-lits
  (defiteration s61v-and-lits (lit1 lit2 out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (litp lit1)
                                (litp lit2)
                                (idp out-id)
                                (s61v-id-in-bounds out-id s61v)
                                (s61v-id-in-bounds (lit-id lit1) s61v)
                                (s61v-id-in-bounds (lit-id lit2) s61v))
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (s61v-id-set out-id n
                 (logand
                  (logxor (bit-extend (lit-neg lit1))
                          (s61v-id-get (lit-id lit1) n s61v))
                  (logxor (bit-extend (lit-neg lit2))
                          (s61v-id-get (lit-id lit2) n s61v)))
                 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-and-lits-iter)))

  (defthm memo-tablep-s61v-and-lits-iter
    (implies (memo-tablep (cdr s61v) aignet)
             (memo-tablep (cdr (s61v-and-lits-iter n lit1 lit2 out-id s61v)) aignet))
    :hints(("Goal" :in-theory (enable memo-tablep))))

  (defthm car-s61v-and-lits-iter
    (equal (car (s61v-and-lits-iter n lit1 lit2 out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-and-lits-iter
    (implies (< (id-val out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-and-lits-iter n lit1 lit2 out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-and-lits-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-and-lits-iter m lit1 lit2 id
                                                              s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-and-lits-iter
    (equal (nth slot (nth n (cdr (s61v-and-lits-iter m lit1 lit2 id s61v))))
           (if (and (equal (nfix n) (id-val id))
                    (< (nfix slot) (nfix m)))
               (logand (logxor (bit-extend (lit-neg lit1))
                               (nth slot (nth (id-val (lit-id lit1)) (cdr
                                                                      s61v))))
                       (logxor (bit-extend (lit-neg lit2))
                               (nth slot (nth (id-val (lit-id lit2)) (cdr s61v)))))
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-and-lits-iter m lit1 lit2 id s61v))))


  (defthm vecsim-to-eval-of-s61v-and-lits-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-and-lits-iter slot1 lit1 lit2 m s61v) aignet-vals aignet)
           (let ((aignet-vals (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)))
             (if (and (< (id-val m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth (id-val m)
                             (b-and
                              (b-xor (lit-neg lit1)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (id-val (lit-id lit1))
                                                     (cdr s61v)))))
                              (b-xor (lit-neg lit2)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (id-val (lit-id lit2))
                                                     (cdr s61v))))))
                             aignet-vals)
               aignet-vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v aignet-vals
                                            aignet)))))))

(defsection s61v-zero
  (defiteration s61v-zero (out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (idp out-id)
                                (s61v-id-in-bounds out-id s61v))
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (s61v-id-set out-id n 0 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-zero-iter)))

  (defthm memo-tablep-s61v-zero-iter
    (implies (memo-tablep (cdr s61v) aignet)
             (memo-tablep (cdr (s61v-zero-iter n out-id s61v)) aignet))
    :hints(("Goal" :in-theory (enable memo-tablep))))

  (defthm car-s61v-zero-iter
    (equal (car (s61v-zero-iter n out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-zero-iter
    (implies (< (id-val out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-zero-iter n out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-zero-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-zero-iter m id s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-zero-iter
    (equal (nth slot (nth n (cdr (s61v-zero-iter m id s61v))))
           (if (and (equal (nfix n) (id-val id))
                    (< (nfix slot) (nfix m)))
               0
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-zero-iter m id s61v))))


  (defthm vecsim-to-eval-of-s61v-zero-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-zero-iter slot1 m s61v) aignet-vals aignet)
           (let ((aignet-vals (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)))
             (if (and (< (id-val m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth (id-val m)
                             0 aignet-vals)
               aignet-vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v
                                            aignet-vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v aignet-vals
                                            aignet)))))))


(defsection aignet-vecsim
  (defiteration aignet-vecsim (s61v aignet)
    (declare (xargs :stobjs (s61v aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (s61v-sizedp s61v aignet))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (mbe :logic (if (gate-orderedp nid aignet)
                                (s61v-and-lits f0 f1 nid s61v)
                              (s61v-zero nid s61v))
                     :exec (s61v-and-lits f0 f1 nid s61v)))
       :out   (b* ((f0 (snode-co->fanin slot0)))
                (mbe :logic (if (co-orderedp nid aignet)
                                (s61v-copy-lit f0 nid s61v)
                              (s61v-zero nid s61v))
                     :exec (s61v-copy-lit f0 nid s61v)))
       :const (s61v-zero nid s61v)
       :in    s61v))
    :returns s61v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (defiteration aignet-vecsim-frame (s61v aignet)
    (declare (xargs :stobjs (s61v aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (s61v-sizedp s61v aignet))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-seq-case
       type (io-id->regp nid aignet)
       :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (mbe :logic (if (gate-orderedp nid aignet)
                                (s61v-and-lits f0 f1 nid s61v)
                              (s61v-zero nid s61v))
                     :exec (s61v-and-lits f0 f1 nid s61v)))
       :pi    s61v
       :ro    (b* ((ri (regnum->id (io-id->ionum nid aignet) aignet)))
                (s61v-copy-lit (mk-lit ri 0) nid s61v))
       :co    (b* ((f0 (snode-co->fanin slot0)))
                (mbe :logic (if (co-orderedp nid aignet)
                                (s61v-copy-lit f0 nid s61v)
                              (s61v-zero nid s61v))
                     :exec (s61v-copy-lit f0 nid s61v)))
       :const (s61v-zero nid s61v)))
    :returns s61v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (local (in-theory (enable aignet-vecsim-iter aignet-vecsim-frame-iter)))

  (defthm memo-tablep-aignet-vecsim-iter
    (implies (memo-tablep (cdr s61v) aignet)
             (memo-tablep (cdr (aignet-vecsim-iter n s61v aignet)) aignet)))



  (local (defthm nfix-less-than-0
           (equal (< (nfix n) 0)
                  nil)))


  (local (defthm aignet-eval-frame1-preserves-prev
           (implies (<= (nfix m) (nfix n))
                    (equal (nth n (aignet-eval-frame1-iter m aignet-vals aignet))
                           (nth n aignet-vals)))
           :hints(("Goal" :in-theory (enable aignet-eval-frame1-iter)))))

  (local (defthm co-orderedp-implies
           (implies (co-orderedp id aignet)
                    (< (id-val (lit-id (co-node->fanin (nth-node id
                                                                 (nth *nodesi*
                                                                      aignet)))))
                       (id-val id)))
           :hints(("Goal" :in-theory (enable co-orderedp)))
           :rule-classes :linear))

  (local (defthm gate-orderedp-implies
           (implies (gate-orderedp id aignet)
                    (and (< (id-val (lit-id (gate-node->fanin0 (nth-node id
                                                                         (nth *nodesi*
                                                                              aignet)))))
                            (id-val id))
                         (< (id-val (lit-id (gate-node->fanin1 (nth-node id
                                                                         (nth *nodesi*
                                                                              aignet)))))
                            (id-val id))))
           :hints(("Goal" :in-theory (enable gate-orderedp)))
           :rule-classes :linear))

  (defthm aignet-vecsim-iter-lookup-prev
    (implies (<= (nfix n) (nfix m))
             (equal (nth slot (nth m (cdr (aignet-vecsim-iter n s61v aignet))))
                    (nth slot (nth m (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n s61v aignet))))

  (defthm car-of-aignet-vecsim-iter
    (equal (car (aignet-vecsim-iter n s61v aignet))
           (car s61v))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n s61v aignet))))

  (defthmd nth-in-aignet-vecsim-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth slot (nth m (cdr (aignet-vecsim-iter n aignet-vals
                                                              aignet))))
                    (nth slot (nth m (cdr (aignet-vecsim-iter nm aignet-vals
                                                              aignet))))))
    :hints (("goal" :induct (aignet-vecsim-iter n aignet-vals aignet)
             :in-theory (disable acl2::b-xor acl2::b-and
                                 (:definition aignet-vecsim-iter)
                                 co-orderedp
                                 gate-orderedp)
             :expand ((aignet-vecsim-iter n aignet-vals aignet)))
            (and stable-under-simplificationp
                 '(:expand ((aignet-vecsim-iter (+ 1 (nfix m))
                                                aignet-vals
                                                aignet))))))

  (local (in-theory (enable nth-in-aignet-vecsim-iter-preserved)))


  (local (defthm aignet-vecsim-stores-id-evals-lemma
           (implies (and (aignet-well-formedp aignet)
                         (aignet-idp id aignet)
                         (< (id-val id) (nfix n))
                         (< (nfix slot) (s61v-ncols s61v)))
                    (acl2::bit-equiv
                     (acl2::logbit bit (nth slot
                                            (nth (id-val id) (cdr
                                                              (aignet-vecsim-iter
                                                               n s61v
                                                               aignet)))))
                     (let* ((aignet-vals
                             (vecsim-to-eval slot bit s61v aignet-vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil aignet-vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil aignet-vals aignet)))
                       (id-eval id in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (e/d (lit-eval)
                                          (id-eval
                                           aignet-vecsim-iter))
                   :induct (id-eval-ind id aignet)
                   :expand ((:free (in-vals reg-vals) (id-eval id in-vals reg-vals aignet))
                            (aignet-vecsim-iter (+ 1 (id-val id))
                                                s61v aignet)
                            (aignet-vecsim-iter 1 s61v aignet))))))

  (defthm aignet-vecsim-iter-correct
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp (to-id m) aignet)
                  (< (nfix m) (nfix n))
                  (< (nfix slot) (s61v-ncols s61v)))
             (equal (acl2::logbit bit (nth slot (nth m (cdr (aignet-vecsim-iter n s61v aignet)))))
                    (let* ((aignet-vals
                             (vecsim-to-eval slot bit s61v aignet-vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil aignet-vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil aignet-vals aignet)))
                      (id-eval (to-id m) in-vals reg-vals aignet))))
    :hints (("goal" :use ((:instance aignet-vecsim-stores-id-evals-lemma
                           (id (to-id m))))
             :in-theory (disable aignet-vecsim-stores-id-evals-lemma
                                 aignet-vecsim-iter
                                 vecsim-to-eval
                                 id-eval)
             :do-not-induct t)))

  (defthmd lookup-in-vecsim-to-eval-iter-equivalent
    (implies (and (equal (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)
                         (aignet-eval-iter n aignet-vals2 aignet))
                  (< (nfix m) (nfix n)))
             (equal (logbitp bit (nth slot (nth m (cdr s61v))))
                    (equal (nth m (aignet-eval-iter n aignet-vals2 aignet))
                           1))))

  (defthmd lookup-in-vecsim-to-eval-frame1-iter-equivalent
    (implies (and (equal (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet)
                         (aignet-eval-frame1-iter n1 aignet-vals2 aignet))
                  (< (nfix m) (nfix n)))
             (equal (logbitp bit (nth slot (nth m (cdr s61v))))
                    (equal (nth m (aignet-eval-frame1-iter n1 aignet-vals2 aignet))
                           1))))

  (local (in-theory (disable (:definition aignet-vecsim-iter))))

  (local (in-theory (disable nth-in-aignet-vecsim-iter-preserved)))

  (defthm aignet-vecsim-iter-to-eval
    (implies (< (nfix slot) (s61v-ncols s61v))
             (equal (vecsim-to-eval-iter n slot bit (aignet-vecsim-iter n s61v aignet) aignet-vals aignet)
                    (aignet-eval-iter n (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet) aignet)))
    :hints (("goal" :induct (aignet-vecsim-iter n s61v aignet)
             :expand ((aignet-vecsim-iter n s61v aignet)
                      (:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v aignet-vals aignet))
                      (:free (aignet-vals)
                       (aignet-eval-iter n aignet-vals aignet)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               lookup-in-vecsim-to-eval-iter-equivalent)))))

  (local (in-theory (disable (:definition aignet-vecsim-frame-iter))))

  (defthm car-aignet-vecsim-frame-iter
    (equal (car (aignet-vecsim-frame-iter n s61v aignet))
           (car s61v))
    :hints ((acl2::just-induct-and-expand
             (aignet-vecsim-frame-iter n s61v aignet))))

  (defthm nth-previous-of-aignet-vecsim-frame-iter
    (implies (<= (nfix n) (nfix m))
             (equal (nth slot (nth m (cdr (aignet-vecsim-frame-iter n s61v aignet))))
                    (nth slot (nth m (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vecsim-frame-iter n s61v aignet))))

  (local (in-theory (enable (:induction aignet-eval-frame1-iter))))

  (defthm nth-previous-of-aignet-eval-frame1-iter
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-frame1-iter n aignet-vals aignet))
                    (nth m aignet-vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame1-iter n aignet-vals aignet))))

  (local (in-theory (disable aignet-eval-frame1-iter-rw)))

  (defthm aignet-vecsim-frame-iter-to-eval
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix slot) (s61v-ncols s61v))
                  (<= (nfix n) (nfix (nth *num-nodes* aignet))))
             (equal (vecsim-to-eval-iter (nth *num-nodes* aignet) slot bit (aignet-vecsim-frame-iter n s61v aignet) aignet-vals aignet)
                    (aignet-eval-frame1-iter n (vecsim-to-eval slot bit s61v aignet-vals aignet) aignet)))
    :hints (("goal" :induct (aignet-vecsim-frame-iter n s61v aignet)
             :expand ((aignet-vecsim-frame-iter n s61v aignet)
                      (:free (aignet-vals)
                       (aignet-eval-frame1-iter n aignet-vals aignet)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               lookup-in-vecsim-to-eval-frame1-iter-equivalent)))
            (and stable-under-simplificationp
                 '(:cases ((< (ID-VAL
                               (NTH-ID (IO-NODE->IONUM (NTH-NODE (TO-ID (+ -1 N))
                                                                 (NTH *NODESI* AIGNET)))
                                       (NTH *REGSI* AIGNET)))
                              (1- n))))))))


