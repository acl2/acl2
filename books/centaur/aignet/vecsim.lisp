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
(include-book "eval")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable nth update-nth set::double-containment)))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable acl2::make-list-ac-removal)))

(acl2::def2darr s61v
                :elt-type (signed-byte 61)
                :elt-typep (lambda (x) (signed-byte-p 61 x))
                :default-elt 0
                :elt-fix ifix
                :elt-guard (integerp x)
                :elt-okp (and (<= x (1- (expt 2 60)))
                              (<= (- (expt 2 60)) x)))

;; (defun s61v-sizedp (s61v aignet)
;;   (declare (xargs :stobjs (s61v aignet)
;;                   :guard-hints ('(:in-theory (enable memo-tablep
;;                                                      acl2::aignetp)))))
;;   (mbe :logic (non-exec (memo-tablep (cdr s61v) aignet))
;;        :exec (<= (num-nodes aignet) (s61v-nrows s61v))))

;; (defun s61v-id-in-bounds (id s61v)
;;   (declare (xargs :guard (idp id)
;;                   :stobjs s61v
;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
;;   (mbe :logic (non-exec (id-in-bounds id (cdr s61v)))
;;        :exec (< (id-val id) (s61v-nrows s61v))))

;; (defun s61v-iterator-in-bounds (n s61v)
;;   (declare (xargs :guard (natp n)
;;                   :stobjs s61v
;;                   :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
;;   (mbe :logic (non-exec (iterator-in-bounds n (cdr s61v)))
;;        :exec (<= (nfix n) (s61v-nrows s61v))))


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

  (defiteration vecsim-to-eval (slot bit s61v vals aignet)
    (declare (type (integer 0 *) slot)
             (type (integer 0 *) bit)
             (xargs :stobjs (s61v vals aignet)
                    :guard (and (<= (num-nodes aignet) (s61v-nrows s61v))
                                (<= (num-nodes aignet) (bits-length vals))
                                (< slot (s61v-ncols s61v)))))
    (b* ((nid (lnfix n))
         (slotval (s61v-get2 nid slot s61v))
         (bitval (acl2::logbit bit slotval))
         (vals (set-bit nid bitval vals)))
      vals)
    :returns vals
    :index n
    :last (num-nodes aignet))

  (in-theory (disable vecsim-to-eval))
  (local (in-theory (enable vecsim-to-eval-iter
                            vecsim-to-eval)))

  (defthm lookup-in-vecsim-to-eval-iter
    (equal (nth m (vecsim-to-eval-iter n slot bit s61v vals aignet))
           (if (<= (nfix n) (nfix m))
               (nth m vals)
             (acl2::logbit bit (s61v-get2 m slot s61v)))))

  (defthm lookup-in-vecsim-to-eval
    (equal (nth m (vecsim-to-eval slot bit s61v vals aignet))
           (if (<= (num-nodes aignet) (nfix m))
               (nth m vals)
             (acl2::logbit bit (s61v-get2 m slot s61v)))))

  ;; (defthm vecsim-to-eval-iter-of-update-eval-prev
  ;;   (equal (vecsim-to-eval-iter n slot bit s61v
  ;;                          (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                                      vals)
  ;;                          aignet)
  ;;          (let ((vals (vecsim-to-eval-iter n slot bit s61v vals aignet)))
  ;;            (if (< (nfix m) (nfix n))
  ;;                vals
  ;;              (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                          vals))))
  ;;   :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v vals aignet)
  ;;            :expand ((:free (vals)
  ;;                      (vecsim-to-eval-iter n slot bit s61v vals aignet))))))
  )


(defsection s61v-copy-lit
  (defiteration s61v-copy-lit (in-lit out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (litp in-lit)
                                (natp out-id)
                                (< out-id (s61v-nrows s61v))
                                (< (lit-id in-lit) (s61v-nrows s61v)))))
    (s61v-set2 out-id n
                 (logxor (bit-extend (lit-neg in-lit))
                         (s61v-get2 (lit-id in-lit) n s61v))
                 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-copy-lit-iter)))

  (defthm memo-tablep-s61v-copy-lit-iter
    (implies (< (node-count aignet) (len (cdr s61v)))
             (< (node-count aignet) (len (cdr (s61v-copy-lit-iter n in-lit out-id s61v)))))
    :rule-classes :linear)

  (defthm car-s61v-copy-lit-iter
    (equal (car (s61v-copy-lit-iter n in-lit out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-copy-lit-iter
    (implies (< (nfix out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-copy-lit-iter n in-lit out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-copy-lit-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-copy-lit-iter m in-lit id
                                                              s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-copy-lit-iter
    (equal (nth slot (nth n (cdr (s61v-copy-lit-iter m in-lit id s61v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logxor (bit-extend (lit-neg in-lit))
                       (nth slot (nth (lit-id in-lit) (cdr s61v))))
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-copy-lit-iter m in-lit id s61v))))


  (defthm vecsim-to-eval-of-s61v-copy-lit-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-copy-lit-iter slot1 in-lit m s61v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s61v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (acl2::b-xor (lit-neg in-lit)
                                          (acl2::logbit bit (nth
                                                             slot
                                                             (nth
                                                              (lit-id
                                                               in-lit)
                                                              (cdr s61v)))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v
                                            vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v vals
                                            aignet)))))))

(defsection s61v-and-lits
  (defiteration s61v-and-lits (lit1 lit2 out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (litp lit1)
                                (litp lit2)
                                (natp out-id)
                                (< out-id (s61v-nrows s61v))
                                (< (lit-id lit1) (s61v-nrows s61v))
                                (< (lit-id lit2) (s61v-nrows s61v)))))
    (s61v-set2 out-id n
                 (logand
                  (logxor (bit-extend (lit-neg lit1))
                          (s61v-get2 (lit-id lit1) n s61v))
                  (logxor (bit-extend (lit-neg lit2))
                          (s61v-get2 (lit-id lit2) n s61v)))
                 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-and-lits-iter)))

  (defthm memo-tablep-s61v-and-lits-iter
    (implies (< (node-count aignet) (len (cdr s61v)))
             (< (node-count aignet) (len (cdr (s61v-and-lits-iter n lit1 lit2 out-id s61v)))))
    :rule-classes :linear)

  (defthm car-s61v-and-lits-iter
    (equal (car (s61v-and-lits-iter n lit1 lit2 out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-and-lits-iter
    (implies (< (nfix out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-and-lits-iter n lit1 lit2 out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-and-lits-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-and-lits-iter m lit1 lit2 id
                                                              s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-and-lits-iter
    (equal (nth slot (nth n (cdr (s61v-and-lits-iter m lit1 lit2 id s61v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logand (logxor (bit-extend (lit-neg lit1))
                               (nth slot (nth (lit-id lit1) (cdr
                                                                      s61v))))
                       (logxor (bit-extend (lit-neg lit2))
                               (nth slot (nth (lit-id lit2) (cdr s61v)))))
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-and-lits-iter m lit1 lit2 id s61v))))


  (defthm vecsim-to-eval-of-s61v-and-lits-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-and-lits-iter slot1 lit1 lit2 m s61v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s61v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (b-and
                              (b-xor (lit-neg lit1)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (lit-id lit1)
                                                     (cdr s61v)))))
                              (b-xor (lit-neg lit2)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (lit-id lit2)
                                                     (cdr s61v))))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v vals
                                            aignet)))))))

(defsection s61v-zero
  (defiteration s61v-zero (out-id s61v)
    (declare (xargs :stobjs s61v
                    :guard (and (natp out-id)
                                (< out-id (s61v-nrows s61v)))))
    (s61v-set2 out-id n 0 s61v)
    :returns s61v
    :index n
    :last (s61v-ncols s61v))

  (local (in-theory (enable s61v-zero-iter)))

  (defthm memo-tablep-s61v-zero-iter
    (implies (< (node-count aignet) (len (cdr s61v)))
             (< (node-count aignet) (len (cdr (s61v-zero-iter n out-id s61v)))))
    :rule-classes :linear)

  (defthm car-s61v-zero-iter
    (equal (car (s61v-zero-iter n out-id s61v))
           (car s61v)))

  (defthm len-cdr-s61v-zero-iter
    (implies (< (nfix out-id) (len (cdr s61v)))
             (equal (len (cdr (s61v-zero-iter n out-id s61v)))
                    (len (cdr s61v)))))

  (defthm lookup-prev-in-s61v-zero-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (cdr (s61v-zero-iter m id s61v))))
                    (nth slot (nth n (cdr s61v))))))

  (defthm lookup-in-s61v-zero-iter
    (equal (nth slot (nth n (cdr (s61v-zero-iter m id s61v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               0
             (nth slot (nth n (cdr s61v)))))
    :hints ((acl2::just-induct-and-expand
             (s61v-zero-iter m id s61v))))


  (defthm vecsim-to-eval-of-s61v-zero-iter
    (equal (vecsim-to-eval-iter n slot bit (s61v-zero-iter slot1 m s61v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s61v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m 0 vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s61v
                                            vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s61v)
                       (vecsim-to-eval-iter n slot bit s61v vals
                                            aignet)))))))


(defsection aignet-vecsim
  (defiteration aignet-vecsim (s61v aignet)
    (declare (xargs :stobjs (s61v aignet)
                    :guard (<= (num-nodes aignet) (s61v-nrows s61v))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (s61v-and-lits f0 f1 nid s61v))
       :out   (b* ((f0 (snode->fanin slot0)))
                (s61v-copy-lit f0 nid s61v))
       :const (s61v-zero nid s61v)
       :in    s61v))
    :returns s61v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (defthm car-nonnil-forward-to-consp
    (implies (car x)
             (consp x))
    :rule-classes :forward-chaining)

  (defiteration aignet-vecsim-frame (s61v aignet)
    (declare (xargs :stobjs (s61v aignet)
                    :guard (<= (num-nodes aignet) (s61v-nrows s61v))
                    :guard-hints ((and stable-under-simplificationp
                                       '(:in-theory (enable aignet-idp))))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-seq-case
       type (io-id->regp nid aignet)
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (s61v-and-lits f0 f1 nid s61v))
       :pi    s61v
       :reg   (b* ((ri (reg-id->nxst (regnum->id (io-id->ionum nid aignet)
                                                 aignet)
                                     aignet)))
                (s61v-copy-lit (mk-lit ri 0) nid s61v))
       :co    (b* ((f0 (snode->fanin slot0)))
                (s61v-copy-lit f0 nid s61v))
       :const (s61v-zero nid s61v)))
    :returns s61v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (local (in-theory (enable aignet-vecsim-iter aignet-vecsim-frame-iter)))

  (defthm memo-tablep-aignet-vecsim-iter
    (implies (< (node-count aignet) (len (cdr s61v)))
             (< (node-count aignet) (len (cdr (aignet-vecsim-iter n s61v aignet)))))
    :rule-classes :linear)



  (local (defthm nfix-less-than-0
           (equal (< (nfix n) 0)
                  nil)))


  ;; (local (defthm aignet-eval-frame1-preserves-prev
  ;;          (implies (<= (nfix m) (nfix n))
  ;;                   (equal (nth n (aignet-eval-frame1-iter m vals aignet))
  ;;                          (nth n vals)))
  ;;          :hints(("Goal" :in-theory (enable aignet-eval-frame1-iter)))))

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
             (equal (nth slot (nth m (cdr (aignet-vecsim-iter n vals
                                                              aignet))))
                    (nth slot (nth m (cdr (aignet-vecsim-iter nm vals
                                                              aignet))))))
    :hints (("goal" :induct (aignet-vecsim-iter n vals aignet)
             :in-theory (disable acl2::b-xor acl2::b-and
                                 (:definition aignet-vecsim-iter))
             :expand ((aignet-vecsim-iter n vals aignet)))
            (and stable-under-simplificationp
                 '(:expand ((aignet-vecsim-iter (+ 1 (nfix m))
                                                vals
                                                aignet))))))

  (local (in-theory (enable nth-in-aignet-vecsim-iter-preserved)))


  (local (defthm aignet-vecsim-stores-id-evals-lemma
           (implies (and (aignet-idp id aignet)
                         (< (nfix id) (nfix n))
                         (< (nfix slot) (s61v-ncols s61v)))
                    (acl2::bit-equiv
                     (acl2::logbit bit (nth slot
                                            (nth id (cdr (aignet-vecsim-iter
                                                          n s61v
                                                          aignet)))))
                     (let* ((vals
                             (vecsim-to-eval slot bit s61v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                       (id-eval id in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (e/d (lit-eval eval-and-of-lits)
                                          (id-eval
                                           aignet-vecsim-iter))
                   :induct (id-eval-ind id aignet)
                   :expand ((:free (in-vals reg-vals) (id-eval id in-vals reg-vals aignet))
                            (aignet-vecsim-iter (+ 1 (nfix id))
                                                s61v aignet)
                            (aignet-vecsim-iter 1 s61v aignet))))))

  (defthm aignet-vecsim-iter-correct
    (implies (and (aignet-idp m aignet)
                  (< (nfix m) (nfix n))
                  (< (nfix slot) (s61v-ncols s61v)))
             (equal (acl2::logbit bit (nth slot (nth m (cdr (aignet-vecsim-iter n s61v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit s61v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                      (id-eval m in-vals reg-vals aignet))))
    :hints (("goal" :use ((:instance aignet-vecsim-stores-id-evals-lemma
                           (id m)))
             :in-theory (disable aignet-vecsim-stores-id-evals-lemma
                                 aignet-vecsim-iter
                                 vecsim-to-eval
                                 id-eval)
             :do-not-induct t)))

  (defthm aignet-vecsim-correct
    (implies (and (aignet-idp m aignet)
                  (< (nfix m) (num-nodes aignet))
                  (< (nfix slot) (s61v-ncols s61v)))
             (equal (acl2::logbit bit (nth slot (nth m (cdr (aignet-vecsim s61v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit s61v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                      (id-eval m in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (disable bitops::logbit-to-logbitp
                                       aignet-vecsim-iter))))


  (defthm aignet-eval-iter-out-of-bounds
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-iter n vals aignet))
                    (nth m vals)))
    :hints((acl2::just-induct-and-expand
            (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-out-of-bounds
    (implies (< (node-count aignet) (nfix m))
             (equal (nth m (aignet-eval vals aignet))
                    (nth m vals)))
    :hints(("Goal" :in-theory (enable aignet-eval))))

  (defthm aignet-vecsim-to-eval-lemma
    (implies (< (nfix slot) (s61v-ncols s61v))
             (bit-equiv
              (nth id (vecsim-to-eval slot bit (aignet-vecsim s61v aignet) vals aignet))
              (nth id (aignet-eval (vecsim-to-eval slot bit s61v vals
                                                   aignet) aignet))))
    :hints (("goal" :in-theory (e/d (aignet-idp)
                                    (bitops::logbit-to-logbitp
                                     aignet-vecsim))
             :cases ((aignet-idp id aignet)))))

  (defthm aignet-vecsim-to-eval
    (implies (< (nfix slot) (s61v-ncols s61v))
             (bits-equiv
              (vecsim-to-eval slot bit (aignet-vecsim s61v aignet) vals aignet)
              (aignet-eval (vecsim-to-eval slot bit s61v vals aignet) aignet)))
    :hints (("goal" :in-theory (disable aignet-vecsim))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))
