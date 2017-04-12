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
(include-book "centaur/bitops/fast-logext" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (disable nth update-nth set::double-containment)))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable acl2::make-list-ac-removal)))

(acl2::def-2d-arr u32v
  :pred (lambda (x) (unsigned-byte-p 32 x))
  :type-decl (unsigned-byte 32)
  :default-val 0
  :fix ifix
  :elt-guard (integerp x)
  :elt-okp (unsigned-byte-p 32 x))

;; (defun u32v-sizedp (u32v aignet)
;;   (declare (xargs :stobjs (u32v aignet)
;;                   :guard-hints ('(:in-theory (enable memo-tablep
;;                                                      acl2::aignetp)))))
;;   (mbe :logic (non-exec (memo-tablep (cdr u32v) aignet))
;;        :exec (<= (num-nodes aignet) (u32v-nrows u32v))))

;; (defun u32v-id-in-bounds (id u32v)
;;   (declare (xargs :guard (idp id)
;;                   :stobjs u32v
;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
;;   (mbe :logic (non-exec (id-in-bounds id (cdr u32v)))
;;        :exec (< (id-val id) (u32v-nrows u32v))))

;; (defun u32v-iterator-in-bounds (n u32v)
;;   (declare (xargs :guard (natp n)
;;                   :stobjs u32v
;;                   :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
;;   (mbe :logic (non-exec (iterator-in-bounds n (cdr u32v)))
;;        :exec (<= (nfix n) (u32v-nrows u32v))))


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

  (defiteration vecsim-to-eval (slot bit u32v vals aignet)
    (declare (type (integer 0 *) slot)
             (type (integer 0 *) bit)
             (xargs :stobjs (u32v vals aignet)
                    :guard (and (<= (num-nodes aignet) (u32v-nrows u32v))
                                (<= (num-nodes aignet) (bits-length vals))
                                (< slot (u32v-ncols u32v)))))
    (b* ((nid (lnfix n))
         (slotval (u32v-get2 nid slot u32v))
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
    (equal (nth m (vecsim-to-eval-iter n slot bit u32v vals aignet))
           (if (<= (nfix n) (nfix m))
               (nth m vals)
             (acl2::logbit bit (u32v-get2 m slot u32v)))))

  (defthm lookup-in-vecsim-to-eval
    (equal (nth m (vecsim-to-eval slot bit u32v vals aignet))
           (if (<= (num-nodes aignet) (nfix m))
               (nth m vals)
             (acl2::logbit bit (u32v-get2 m slot u32v)))))

  ;; (defthm vecsim-to-eval-iter-of-update-eval-prev
  ;;   (equal (vecsim-to-eval-iter n slot bit u32v
  ;;                          (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                                      vals)
  ;;                          aignet)
  ;;          (let ((vals (vecsim-to-eval-iter n slot bit u32v vals aignet)))
  ;;            (if (< (nfix m) (nfix n))
  ;;                vals
  ;;              (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                          vals))))
  ;;   :hints (("goal" :induct (vecsim-to-eval-iter n slot bit u32v vals aignet)
  ;;            :expand ((:free (vals)
  ;;                      (vecsim-to-eval-iter n slot bit u32v vals aignet))))))
  )


(defsection u32v-copy-lit

  (defiteration u32v-copy-lit (in-lit out-id u32v)
    (declare (xargs :stobjs u32v
                    :guard (and (litp in-lit)
                                (natp out-id)
                                (< out-id (u32v-nrows u32v))
                                (< (lit-id in-lit) (u32v-nrows u32v)))))
    (u32v-set2 out-id n
               (logxor (bit-extend (lit-neg in-lit))
                       (u32v-get2 (lit-id in-lit) n u32v))
               u32v)
    :returns u32v
    :index n
    :last (u32v-ncols u32v))

  (local (in-theory (enable u32v-copy-lit-iter)))

  (defthm memo-tablep-u32v-copy-lit-iter
    (implies (< (node-count aignet) (len (stobjs::2darr->rows u32v)))
             (< (node-count aignet) (len (stobjs::2darr->rows (u32v-copy-lit-iter n in-lit out-id u32v)))))
    :rule-classes :linear)

  (defthm max-fanin-memo-tablep-u32v-copy-lit-iter
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows (u32v-copy-lit-iter n in-lit out-id u32v)))))
    :rule-classes :linear)

  (defthm ncols-u32v-copy-lit-iter
    (equal (stobjs::2darr->ncols (u32v-copy-lit-iter n in-lit out-id u32v))
           (stobjs::2darr->ncols u32v)))

  (defthm len-cdr-u32v-copy-lit-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows (u32v-copy-lit-iter n in-lit out-id u32v)))
                    (len (stobjs::2darr->rows u32v)))))

  (defthm lookup-prev-in-u32v-copy-lit-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (u32v-copy-lit-iter m in-lit id
                                                              u32v))))
                    (nth slot (nth n (stobjs::2darr->rows u32v))))))

  (defthm lookup-in-u32v-copy-lit-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (u32v-copy-lit-iter m in-lit id u32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logxor (bit-extend (lit-neg in-lit))
                       (nth slot (nth (lit-id in-lit) (stobjs::2darr->rows u32v))))
             (nth slot (nth n (stobjs::2darr->rows u32v)))))
    :hints ((acl2::just-induct-and-expand
             (u32v-copy-lit-iter m in-lit id u32v))))


  (defthm vecsim-to-eval-of-u32v-copy-lit-iter
    (equal (vecsim-to-eval-iter n slot bit (u32v-copy-lit-iter slot1 in-lit m u32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit u32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (acl2::b-xor (lit-neg in-lit)
                                          (acl2::logbit bit (nth
                                                             slot
                                                             (nth
                                                              (lit-id
                                                               in-lit)
                                                              (stobjs::2darr->rows u32v)))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit u32v
                                                 vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (u32v)
                       (vecsim-to-eval-iter n slot bit u32v vals
                                            aignet)))))))

(defsection u32v-and-lits
  (defiteration u32v-and-lits (lit1 lit2 out-id u32v)
    (declare (xargs :stobjs u32v
                    :guard (and (litp lit1)
                                (litp lit2)
                                (natp out-id)
                                (< out-id (u32v-nrows u32v))
                                (< (lit-id lit1) (u32v-nrows u32v))
                                (< (lit-id lit2) (u32v-nrows u32v)))))
    (u32v-set2 out-id n
                 (logand
                  (logxor (bit-extend (lit-neg lit1))
                          (u32v-get2 (lit-id lit1) n u32v))
                  (logxor (bit-extend (lit-neg lit2))
                          (u32v-get2 (lit-id lit2) n u32v)))
                 u32v)
    :returns u32v
    :index n
    :last (u32v-ncols u32v))

  (local (in-theory (enable u32v-and-lits-iter)))

  (defthm memo-tablep-u32v-and-lits-iter
    (implies (< (node-count aignet) (len (stobjs::2darr->rows u32v)))
             (< (node-count aignet) (len (stobjs::2darr->rows (u32v-and-lits-iter n lit1 lit2 out-id u32v)))))
    :rule-classes :linear)

  (defthm max-fanin-memo-tablep-u32v-and-lits-iter
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows (u32v-and-lits-iter n lit1 lit2 out-id u32v)))))
    :rule-classes :linear)

  (defthm ncols-u32v-and-lits-iter
    (equal (stobjs::2darr->ncols (u32v-and-lits-iter n lit1 lit2 out-id u32v))
           (stobjs::2darr->ncols u32v)))

  (defthm len-cdr-u32v-and-lits-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows (u32v-and-lits-iter n lit1 lit2 out-id u32v)))
                    (len (stobjs::2darr->rows u32v)))))

  (defthm lookup-prev-in-u32v-and-lits-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (u32v-and-lits-iter m lit1 lit2 id
                                                              u32v))))
                    (nth slot (nth n (stobjs::2darr->rows u32v))))))

  (defthm lookup-in-u32v-and-lits-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (u32v-and-lits-iter m lit1 lit2 id u32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logand (logxor (bit-extend (lit-neg lit1))
                               (nth slot (nth (lit-id lit1) (stobjs::2darr->rows
                                                                      u32v))))
                       (logxor (bit-extend (lit-neg lit2))
                               (nth slot (nth (lit-id lit2) (stobjs::2darr->rows u32v)))))
             (nth slot (nth n (stobjs::2darr->rows u32v)))))
    :hints ((acl2::just-induct-and-expand
             (u32v-and-lits-iter m lit1 lit2 id u32v))))


  (defthm vecsim-to-eval-of-u32v-and-lits-iter
    (equal (vecsim-to-eval-iter n slot bit (u32v-and-lits-iter slot1 lit1 lit2 m u32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit u32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (b-and
                              (b-xor (lit-neg lit1)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (lit-id lit1)
                                                     (stobjs::2darr->rows u32v)))))
                              (b-xor (lit-neg lit2)
                                     (acl2::logbit
                                      bit
                                      (nth slot (nth (lit-id lit2)
                                                     (stobjs::2darr->rows u32v))))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit u32v vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (u32v)
                       (vecsim-to-eval-iter n slot bit u32v vals
                                            aignet)))))))

(defsection u32v-zero
  (defiteration u32v-zero (out-id u32v)
    (declare (xargs :stobjs u32v
                    :guard (and (natp out-id)
                                (< out-id (u32v-nrows u32v)))))
    (u32v-set2 out-id n 0 u32v)
    :returns u32v
    :index n
    :last (u32v-ncols u32v))

  (local (in-theory (enable u32v-zero-iter)))

  (defthm memo-tablep-u32v-zero-iter
    (implies (< (node-count aignet) (len (stobjs::2darr->rows u32v)))
             (< (node-count aignet) (len (stobjs::2darr->rows (u32v-zero-iter n out-id u32v)))))
    :rule-classes :linear)

  (defthm max-fanin-memo-tablep-u32v-zero-iter
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows (u32v-zero-iter n out-id u32v)))))
    :rule-classes :linear)

  (defthm ncols-u32v-zero-iter
    (equal (stobjs::2darr->ncols (u32v-zero-iter n out-id u32v))
           (stobjs::2darr->ncols u32v)))

  (defthm len-cdr-u32v-zero-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows (u32v-zero-iter n out-id u32v)))
                    (len (stobjs::2darr->rows u32v)))))

  (defthm lookup-prev-in-u32v-zero-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (u32v-zero-iter m id u32v))))
                    (nth slot (nth n (stobjs::2darr->rows u32v))))))

  (defthm lookup-in-u32v-zero-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (u32v-zero-iter m id u32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               0
             (nth slot (nth n (stobjs::2darr->rows u32v)))))
    :hints ((acl2::just-induct-and-expand
             (u32v-zero-iter m id u32v))))

  


  (defthm vecsim-to-eval-of-u32v-zero-iter
    (equal (vecsim-to-eval-iter n slot bit (u32v-zero-iter slot1 m u32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit u32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m 0 vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit u32v
                                            vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (u32v)
                       (vecsim-to-eval-iter n slot bit u32v vals
                                            aignet)))))))


(defsection u32v-randomize
  (local (defthm random$-bound
           (b* (((mv val ?state) (random$ limit state)))
             (implies (posp limit)
                      (< val limit)))
           :hints(("Goal" :in-theory (enable random$)))
           :rule-classes :linear))

  (local (defthm random$-type
           (b* (((mv val ?state) (random$ limit state)))
             (natp val))
           :hints(("Goal" :in-theory (enable random$)))
           :rule-classes :type-prescription))

  (defiteration u32v-randomize (out-id u32v state)
    (declare (xargs :stobjs (u32v state)
                    :guard (and (natp out-id)
                                (< out-id (u32v-nrows u32v)))))
    (b* (((mv uval state) (random$ (expt 2 32) state))
         (u32v (u32v-set2 out-id n ;; (bitops::fast-logext 32 uval)
                          uval
                          u32v)))
      (mv u32v state))
    :returns (mv u32v state)
    :index n
    :last (u32v-ncols u32v))

  (local (in-theory (enable u32v-randomize-iter)))

  (defthm memo-tablep-u32v-randomize-iter
    (implies (< (node-count aignet) (len (stobjs::2darr->rows u32v)))
             (< (node-count aignet) (len (stobjs::2darr->rows (mv-nth 0 (u32v-randomize-iter n out-id u32v state))))))
    :rule-classes :linear)

  (defthm ncols-u32v-randomize-iter
    (equal (stobjs::2darr->ncols (mv-nth 0 (u32v-randomize-iter n out-id u32v state)))
           (stobjs::2darr->ncols u32v)))

  (defthm len-cdr-u32v-randomize-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows (mv-nth 0 (u32v-randomize-iter n out-id u32v state))))
                    (len (stobjs::2darr->rows u32v)))))

  (defthm lookup-prev-in-u32v-randomize-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (mv-nth 0 (u32v-randomize-iter m id u32v state)))))
                    (nth slot (nth n (stobjs::2darr->rows u32v)))))))


(defsection aignet-vecsim
  (defiteration aignet-vecsim (u32v aignet)
    (declare (xargs :stobjs (u32v aignet)
                    :guard (<= (num-nodes aignet) (u32v-nrows u32v))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (u32v-and-lits f0 f1 nid u32v))
       :out   (b* ((f0 (snode->fanin slot0)))
                (u32v-copy-lit f0 nid u32v))
       :const (u32v-zero nid u32v)
       :in    u32v))
    :returns u32v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (defthm car-nonnil-forward-to-consp
    (implies (car x)
             (consp x))
    :rule-classes :forward-chaining)

  (defiteration aignet-vecsim-frame (u32v aignet)
    (declare (xargs :stobjs (u32v aignet)
                    :guard (<= (num-nodes aignet) (u32v-nrows u32v))
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
                (u32v-and-lits f0 f1 nid u32v))
       :pi    u32v
       :reg   (b* ((ri (reg-id->nxst (regnum->id (io-id->ionum nid aignet)
                                                 aignet)
                                     aignet)))
                (u32v-copy-lit (mk-lit ri 0) nid u32v))
       :co    (b* ((f0 (snode->fanin slot0)))
                (u32v-copy-lit f0 nid u32v))
       :const (u32v-zero nid u32v)))
    :returns u32v
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (local (in-theory (enable aignet-vecsim-iter aignet-vecsim-frame-iter)))

  (defthm memo-tablep-aignet-vecsim-iter
    (implies (< (node-count aignet) (len (stobjs::2darr->rows u32v)))
             (< (node-count aignet) (len (stobjs::2darr->rows (aignet-vecsim-iter n u32v aignet)))))
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
             (equal (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter n u32v aignet))))
                    (nth slot (nth m (stobjs::2darr->rows u32v)))))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n u32v aignet))))

  (defthm ncols-of-aignet-vecsim-iter
    (equal (stobjs::2darr->ncols (aignet-vecsim-iter n u32v aignet))
           (stobjs::2darr->ncols u32v))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n u32v aignet))))

  (defthmd nth-in-aignet-vecsim-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter n vals
                                                              aignet))))
                    (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter nm vals
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
                         (< (nfix slot) (u32v-ncols u32v)))
                    (acl2::bit-equiv
                     (acl2::logbit bit (nth slot
                                            (nth id (stobjs::2darr->rows (aignet-vecsim-iter
                                                          n u32v
                                                          aignet)))))
                     (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
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
                                                u32v aignet)
                            (aignet-vecsim-iter 1 u32v aignet))))))

  (defthm aignet-vecsim-iter-correct
    (implies (and (aignet-idp m aignet)
                  (< (nfix m) (nfix n))
                  (< (nfix slot) (u32v-ncols u32v)))
             (equal (acl2::logbit bit (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter n u32v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
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
                  (< (nfix slot) (u32v-ncols u32v)))
             (equal (acl2::logbit bit (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim u32v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
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
    (implies (< (nfix slot) (u32v-ncols u32v))
             (bit-equiv
              (nth id (vecsim-to-eval slot bit (aignet-vecsim u32v aignet) vals aignet))
              (nth id (aignet-eval (vecsim-to-eval slot bit u32v vals
                                                   aignet) aignet))))
    :hints (("goal" :in-theory (e/d (aignet-idp)
                                    (bitops::logbit-to-logbitp
                                     aignet-vecsim))
             :cases ((aignet-idp id aignet)))))

  (defthm aignet-vecsim-to-eval
    (implies (< (nfix slot) (u32v-ncols u32v))
             (bits-equiv
              (vecsim-to-eval slot bit (aignet-vecsim u32v aignet) vals aignet)
              (aignet-eval (vecsim-to-eval slot bit u32v vals aignet) aignet)))
    :hints (("goal" :in-theory (disable aignet-vecsim))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))



(defsection aignet-vecsim*
  ;; Same as aignet-vecsim, but does not process output nodes and therefore
  ;; only needs max-fanin+1 entries.  Note: we can't have a version of
  ;; aignet-vecsim-frame that works this way, because of problems where we
  ;; overwrite some previous-frame value with a next-frame value while that
  ;; previous-frame value is still needed for some register to be updated.
  (defiteration aignet-vecsim* (u32v aignet)
    (declare (xargs :stobjs (u32v aignet)
                    :guard (<= (+ 1 (max-fanin aignet)) (u32v-nrows u32v))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode->fanin slot0))
                   (f1 (gate-id->fanin1 nid aignet)))
                (u32v-and-lits f0 f1 nid u32v))
       :out   u32v
       :const (u32v-zero nid u32v)
       :in    u32v))
    :returns u32v
    :index n
    :last (+ 1 (max-fanin aignet))
    :package aignet::foo)


  (local (in-theory (enable aignet-vecsim*-iter)))

  (defthm max-fanin-memo-tablep-aignet-vecsim*-iter
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows (aignet-vecsim*-iter n u32v aignet)))))
    :rule-classes :linear)



  (local (defthm nfix-less-than-0
           (equal (< (nfix n) 0)
                  nil)))


  ;; (local (defthm aignet-eval-frame1-preserves-prev
  ;;          (implies (<= (nfix m) (nfix n))
  ;;                   (equal (nth n (aignet-eval-frame1-iter m vals aignet))
  ;;                          (nth n vals)))
  ;;          :hints(("Goal" :in-theory (enable aignet-eval-frame1-iter)))))

  (defthm aignet-vecsim*-iter-lookup-prev
    (implies (<= (nfix n) (nfix m))
             (equal (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim*-iter n u32v aignet))))
                    (nth slot (nth m (stobjs::2darr->rows u32v)))))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim*-iter n u32v aignet))))

  (defthm ncols-of-aignet-vecsim*-iter
    (equal (stobjs::2darr->ncols (aignet-vecsim*-iter n u32v aignet))
           (stobjs::2darr->ncols u32v))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim*-iter n u32v aignet))))

  (defthm nrows-of-aignet-vecsim*-iter
    (implies (<= n (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows (aignet-vecsim*-iter n u32v aignet)))
                    (len (stobjs::2darr->rows u32v)))))

  (defthmd nth-in-aignet-vecsim*-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim*-iter n vals
                                                              aignet))))
                    (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim*-iter nm vals
                                                              aignet))))))
    :hints (("goal" :induct (aignet-vecsim*-iter n vals aignet)
             :in-theory (disable acl2::b-xor acl2::b-and
                                 (:definition aignet-vecsim*-iter))
             :expand ((aignet-vecsim*-iter n vals aignet)))
            (and stable-under-simplificationp
                 '(:expand ((aignet-vecsim*-iter (+ 1 (nfix m))
                                                vals
                                                aignet))))))

  (local (in-theory (enable nth-in-aignet-vecsim*-iter-preserved)))


  (local (defthm aignet-vecsim*-stores-id-evals-lemma
           (implies (and (aignet-idp id aignet)
                         (not (equal (ctype (stype (car (lookup-id id aignet))))
                                     :output))
                         (< (nfix id) (nfix n))
                         (< (nfix slot) (u32v-ncols u32v)))
                    (acl2::bit-equiv
                     (acl2::logbit bit (nth slot
                                            (nth id (stobjs::2darr->rows (aignet-vecsim*-iter
                                                          n u32v
                                                          aignet)))))
                     (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                       (id-eval id in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (e/d (lit-eval eval-and-of-lits)
                                          (id-eval
                                           aignet-vecsim*-iter))
                   :induct (id-eval-ind id aignet)
                   :expand ((:free (in-vals reg-vals) (id-eval id in-vals reg-vals aignet))
                            (aignet-vecsim*-iter (+ 1 (nfix id))
                                                u32v aignet)
                            (aignet-vecsim*-iter 1 u32v aignet))))))

  (defthm aignet-vecsim*-iter-correct
    (implies (and (aignet-idp m aignet)
                  (not (equal (ctype (stype (car (lookup-id m aignet))))
                                     :output))
                  (< (nfix m) (nfix n))
                  (< (nfix slot) (u32v-ncols u32v)))
             (equal (acl2::logbit bit (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim*-iter n u32v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                      (id-eval m in-vals reg-vals aignet))))
    :hints (("goal" :use ((:instance aignet-vecsim*-stores-id-evals-lemma
                           (id m)))
             :in-theory (disable aignet-vecsim*-stores-id-evals-lemma
                                 aignet-vecsim*-iter
                                 vecsim-to-eval
                                 id-eval)
             :do-not-induct t)))

  
  (local (defthm aignet-idp-and-not-output-implies-less-than-max-fanin
           (implies (and (aignet-idp n aignet)
                         (not (equal (ctype (stype (car (lookup-id n aignet))))
                                     :output)))
                    (< (nfix n) (+ 1 (node-count (find-max-fanin aignet)))))
           :hints(("Goal" :in-theory (enable find-max-fanin lookup-id aignet-idp)))))

  (defthm aignet-vecsim*-correct
    (implies (and (aignet-idp m aignet)
                  (not (equal (ctype (stype (car (lookup-id m aignet))))
                                     :output))
                  ;; (<= (nfix m) (max-fanin aignet))
                  (< (nfix slot) (u32v-ncols u32v)))
             (equal (acl2::logbit bit (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim* u32v aignet)))))
                    (let* ((vals
                             (vecsim-to-eval slot bit u32v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                      (id-eval m in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (disable bitops::logbit-to-logbitp
                                       aignet-vecsim*-iter))))


  (defthm aignet-eval-iter-out-of-bounds
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-iter n vals aignet))
                    (nth m vals)))
    :hints((acl2::just-induct-and-expand
            (aignet-eval-iter n vals aignet))))


  (defthm aignet-vecsim*-to-eval-lemma
    (implies (and (< (nfix slot) (u32v-ncols u32v))
                  (not (equal (ctype (stype (car (lookup-id id aignet))))
                                     :output))
                  ;; (aignet-idp id aignet)
                  ;; (<= (nfix id) (max-fanin aignet))
                  )
             (bit-equiv
              (nth id (vecsim-to-eval slot bit (aignet-vecsim* u32v aignet) vals aignet))
              (nth id (aignet-eval (vecsim-to-eval slot bit u32v vals
                                                   aignet) aignet))))
    :hints (("goal" :in-theory (e/d (aignet-idp)
                                    (bitops::logbit-to-logbitp
                                     aignet-vecsim*))
             :cases ((aignet-idp id aignet))))))

(define u32v-randomize-inputs ((n natp "start at 0")
                               (u32v)
                               (aignet)
                               (state))
  :guard (and (<= n (num-ins aignet))
              (<= (+ 1 (max-fanin aignet)) (u32v-nrows u32v)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :returns (mv new-u32v new-state)
  (if (mbe :logic (zp (- (num-ins aignet) (nfix n)))
           :exec (eql n (num-ins aignet)))
      (mv u32v state)
    (b* (((mv u32v state) (u32v-randomize (innum->id n aignet) u32v state)))
      (u32v-randomize-inputs (1+ (lnfix n)) u32v aignet state)))
  ///
  (defret ncols-of-u32v-randomize-inputs
    (equal (stobjs::2darr->ncols new-u32v)
           (stobjs::2darr->ncols u32v)))

  (defret nrows-of-u32v-randomize-inputs
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows new-u32v))
                    (len (stobjs::2darr->rows u32v))))))

(define u32v-randomize-regs ((n natp "start at 0")
                             (u32v)
                             (aignet)
                             (state))
  :guard (and (<= n (num-regs aignet))
              (<= (+ 1 (max-fanin aignet)) (u32v-nrows u32v)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (mv new-u32v new-state)
  (if (mbe :logic (zp (- (num-regs aignet) (nfix n)))
           :exec (eql n (num-regs aignet)))
      (mv u32v state)
    (b* (((mv u32v state) (u32v-randomize (regnum->id n aignet) u32v state)))
      (u32v-randomize-regs (1+ (lnfix n)) u32v aignet state)))
  ///
  (defret ncols-of-u32v-randomize-regs
    (equal (stobjs::2darr->ncols new-u32v)
           (stobjs::2darr->ncols u32v)))

  (defret nrows-of-u32v-randomize-regs
    (implies (<= (+ 1 (node-count (find-max-fanin aignet))) (len (stobjs::2darr->rows u32v)))
             (equal (len (stobjs::2darr->rows new-u32v))
                    (len (stobjs::2darr->rows u32v))))))
  
  
