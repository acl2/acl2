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
(local (include-book "std/lists/update-nth" :dir :system))

;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (disable nth update-nth acl2::update-nth-when-zp)))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable signed-byte-p)))
(local (std::add-default-post-define-hook :fix))

;; BOZO skipping node-list-fix congruence proofs here
(local (table fty::fixtypes 'fty::fixtype-alist
              (b* ((fixtype-alist (cdr (assoc 'fty::fixtype-alist (table-alist 'fty::fixtypes world)))))
                (remove-equal (assoc 'aignet fixtype-alist)
                              fixtype-alist))))

(defxdoc vector-simulation
  :parents (aignet-eval)
  :short "Simulating the network by running many tests in parallel using vector logic operations"
  :long " <p>32-bit bitwise logic operations can be used to effectively run 32
ANDs, XORs, or NOTs with one operation, so we can use this to run many
evaluations of an AIG very quickly. See subtopics for various utilities.</p>")


(define s32-fix ((x :type (signed-byte 32)))
  :inline t
  :returns (new-x (signed-byte-p 32 new-x))
  (mbe :logic (acl2::logext 32 x) :exec x)
  ///
  (defthm s32-fix-when-signed-byte-p
    (implies (signed-byte-p 32 x)
             (equal (s32-fix x) x))))

(acl2::def-2d-arr s32v
  :pred (lambda (x) (signed-byte-p 32 x))
  :type-decl (signed-byte 32)
  :default-val 0
  :fix s32-fix
  :parents (vector-simulation)
  :short "Stobj containing a 2-dimensional array of 32-bit signed integers.  Used to store the data for @(see vector-simulation).")

(defthm signed-byte-p-of-s32v-get2
  (signed-byte-p 32 (s32v-get2 row col s32v)))

;; (defun s32v-sizedp (s32v aignet)
;;   (declare (xargs :stobjs (s32v aignet)
;;                   :guard-hints ('(:in-theory (enable memo-tablep
;;                                                      acl2::aignetp)))))
;;   (mbe :logic (non-exec (memo-tablep (cdr s32v) aignet))
;;        :exec (<= (num-fanins aignet) (s32v-nrows s32v))))

;; (defun s32v-id-in-bounds (id s32v)
;;   (declare (xargs :guard (idp id)
;;                   :stobjs s32v
;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
;;   (mbe :logic (non-exec (id-in-bounds id (cdr s32v)))
;;        :exec (< (id-val id) (s32v-nrows s32v))))

;; (defun s32v-iterator-in-bounds (n s32v)
;;   (declare (xargs :guard (natp n)
;;                   :stobjs s32v
;;                   :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
;;   (mbe :logic (non-exec (iterator-in-bounds n (cdr s32v)))
;;        :exec (<= (nfix n) (s32v-nrows s32v))))


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

(defthm signed-byte-32-of-bit-extend
  (signed-byte-p 32 (bit-extend bit))
  :hints(("Goal" :in-theory (enable bit-extend))))

;; (local (in-theory (disable acl2::nth-with-large-index)))

(defsection vecsim-to-eval

  (defiteration vecsim-to-eval (slot bit s32v vals aignet)
    (declare (type (integer 0 *) slot)
             (type (integer 0 *) bit)
             (xargs :stobjs (s32v vals aignet)
                    :guard (and (<= (num-fanins aignet) (s32v-nrows s32v))
                                (<= (num-fanins aignet) (bits-length vals))
                                (< slot (s32v-ncols s32v)))))
    (b* ((nid (lnfix n))
         (slotval (s32v-get2 nid slot s32v))
         (bitval (acl2::logbit bit slotval))
         (vals (set-bit nid bitval vals)))
      vals)
    :returns vals
    :index n
    :last (num-fanins aignet))

  (in-theory (disable vecsim-to-eval))
  (local (in-theory (enable vecsim-to-eval-iter
                            vecsim-to-eval)))

  (defthm lookup-in-vecsim-to-eval-iter
    (equal (nth m (vecsim-to-eval-iter n slot bit s32v vals aignet))
           (if (<= (nfix n) (nfix m))
               (nth m vals)
             (acl2::logbit bit (s32v-get2 m slot s32v)))))

  (defthm lookup-in-vecsim-to-eval
    (equal (nth m (vecsim-to-eval slot bit s32v vals aignet))
           (if (<= (num-fanins aignet) (nfix m))
               (nth m vals)
             (acl2::logbit bit (s32v-get2 m slot s32v)))))

  ;; (defthm vecsim-to-eval-iter-of-update-eval-prev
  ;;   (equal (vecsim-to-eval-iter n slot bit s32v
  ;;                          (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                                      vals)
  ;;                          aignet)
  ;;          (let ((vals (vecsim-to-eval-iter n slot bit s32v vals aignet)))
  ;;            (if (< (nfix m) (nfix n))
  ;;                vals
  ;;              (update-nth *bitsi* (update-nth m val (nth *bitsi* vals))
  ;;                          vals))))
  ;;   :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s32v vals aignet)
  ;;            :expand ((:free (vals)
  ;;                      (vecsim-to-eval-iter n slot bit s32v vals aignet))))))

  (defthm len-of-vecsim-to-eval-iter
    (implies (and (<= (num-fanins aignet) (len vals))
                  (<= (nfix n) (num-fanins aignet)))
             (equal (len (vecsim-to-eval-iter n slot bit s32v vals aignet))
                    (len vals))))

  (defthm len-of-vecsim-to-eval
    (implies (and (<= (num-fanins aignet) (len vals)))
             (equal (len (vecsim-to-eval slot bit s32v vals aignet))
                    (len vals))))
  )


(defsection s32v-copy-lit

  (defiteration s32v-copy-lit (in-lit out-id s32v)
    (declare (xargs :stobjs s32v
                    :guard (and (litp in-lit)
                                (natp out-id)
                                (< out-id (s32v-nrows s32v))
                                (< (lit-id in-lit) (s32v-nrows s32v)))))
    (s32v-set2 out-id n
               (logxor (bit-extend (lit-neg in-lit))
                       (s32v-get2 (lit-id in-lit) n s32v))
               s32v)
    :returns s32v
    :index n
    :last (s32v-ncols s32v))

  (local (in-theory (enable s32v-copy-lit-iter)))

  (defthm memo-tablep-s32v-copy-lit-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-copy-lit-iter n in-lit out-id s32v)))))
    :rule-classes :linear)

  (defthm memo-tablep-s32v-copy-lit-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-copy-lit-iter n in-lit out-id s32v)))))
    :rule-classes :linear)

  (defthm ncols-s32v-copy-lit-iter
    (equal (stobjs::2darr->ncols (s32v-copy-lit-iter n in-lit out-id s32v))
           (stobjs::2darr->ncols s32v)))

  (defthm len-cdr-s32v-copy-lit-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (s32v-copy-lit-iter n in-lit out-id s32v)))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm lookup-prev-in-s32v-copy-lit-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (s32v-copy-lit-iter m in-lit id
                                                              s32v))))
                    (nth slot (nth n (stobjs::2darr->rows s32v))))))

  (defthm lookup-in-s32v-copy-lit-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (s32v-copy-lit-iter m in-lit id s32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logxor (bit-extend (lit-neg in-lit))
                       (s32-fix (nth slot (nth (lit-id in-lit) (stobjs::2darr->rows s32v)))))
             (nth slot (nth n (stobjs::2darr->rows s32v)))))
    :hints ((acl2::just-induct-and-expand
             (s32v-copy-lit-iter m in-lit id s32v))))


  (defthm vecsim-to-eval-of-s32v-copy-lit-iter
    (equal (vecsim-to-eval-iter n slot bit (s32v-copy-lit-iter slot1 in-lit m s32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (acl2::b-xor (lit-neg in-lit)
                                          (acl2::logbit bit (s32-fix
                                                             (nth
                                                              slot
                                                              (nth
                                                               (lit-id
                                                                in-lit)
                                                               (stobjs::2darr->rows s32v))))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s32v
                                                 vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s32v)
                       (vecsim-to-eval-iter n slot bit s32v vals
                                            aignet)))))))

(defsection s32v-and-lits
  (defiteration s32v-and-lits (lit1 lit2 out-id s32v)
    (declare (xargs :stobjs s32v
                    :guard (and (litp lit1)
                                (litp lit2)
                                (natp out-id)
                                (< out-id (s32v-nrows s32v))
                                (< (lit-id lit1) (s32v-nrows s32v))
                                (< (lit-id lit2) (s32v-nrows s32v)))))
    (s32v-set2 out-id n
                 (logand
                  (logxor (bit-extend (lit-neg lit1))
                          (s32v-get2 (lit-id lit1) n s32v))
                  (logxor (bit-extend (lit-neg lit2))
                          (s32v-get2 (lit-id lit2) n s32v)))
                 s32v)
    :returns s32v
    :index n
    :last (s32v-ncols s32v))

  (local (in-theory (enable s32v-and-lits-iter)))

  (defthm memo-tablep-s32v-and-lits-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-and-lits-iter n lit1 lit2 out-id s32v)))))
    :rule-classes :linear)

  (defthm memo-tablep-s32v-and-lits-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-and-lits-iter n lit1 lit2 out-id s32v)))))
    :rule-classes :linear)

  (defthm ncols-s32v-and-lits-iter
    (equal (stobjs::2darr->ncols (s32v-and-lits-iter n lit1 lit2 out-id s32v))
           (stobjs::2darr->ncols s32v)))

  (defthm len-cdr-s32v-and-lits-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (s32v-and-lits-iter n lit1 lit2 out-id s32v)))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm lookup-prev-in-s32v-and-lits-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (s32v-and-lits-iter m lit1 lit2 id
                                                              s32v))))
                    (nth slot (nth n (stobjs::2darr->rows s32v))))))

  (defthm lookup-in-s32v-and-lits-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (s32v-and-lits-iter m lit1 lit2 id s32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logand (logxor (bit-extend (lit-neg lit1))
                               (s32-fix (nth slot (nth (lit-id lit1) (stobjs::2darr->rows
                                                                      s32v)))))
                       (logxor (bit-extend (lit-neg lit2))
                               (s32-fix (nth slot (nth (lit-id lit2) (stobjs::2darr->rows s32v))))))
             (nth slot (nth n (stobjs::2darr->rows s32v)))))
    :hints ((acl2::just-induct-and-expand
             (s32v-and-lits-iter m lit1 lit2 id s32v))))


  (defthm vecsim-to-eval-of-s32v-and-lits-iter
    (equal (vecsim-to-eval-iter n slot bit (s32v-and-lits-iter slot1 lit1 lit2 m s32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (b-and
                              (b-xor (lit-neg lit1)
                                     (acl2::logbit
                                      bit
                                      (s32-fix (nth slot (nth (lit-id lit1)
                                                              (stobjs::2darr->rows s32v))))))
                              (b-xor (lit-neg lit2)
                                     (acl2::logbit
                                      bit
                                      (s32-fix (nth slot (nth (lit-id lit2)
                                                              (stobjs::2darr->rows s32v)))))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s32v vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s32v)
                       (vecsim-to-eval-iter n slot bit s32v vals
                                            aignet)))))))



(local (defthm b-xor-associative
         (equal (b-xor (b-xor x y) z)
                (b-xor x (b-xor y z)))
         :hints(("Goal" :in-theory (enable b-xor)))))
(local (defthm b-xor-commutative2
         (equal (b-xor y (b-xor x z))
                (b-xor x (b-xor y z)))
         :hints(("Goal" :in-theory (enable b-xor)))))

(defsection s32v-xor-lits
  (defiteration s32v-xor-lits (lit1 lit2 out-id s32v)
    (declare (xargs :stobjs s32v
                    :guard (and (litp lit1)
                                (litp lit2)
                                (natp out-id)
                                (< out-id (s32v-nrows s32v))
                                (< (lit-id lit1) (s32v-nrows s32v))
                                (< (lit-id lit2) (s32v-nrows s32v)))))
    (s32v-set2 out-id n
               (logxor (bit-extend (b-xor (lit-neg lit1) (lit-neg lit2)))
                 (logxor (s32v-get2 (lit-id lit1) n s32v)
                         (s32v-get2 (lit-id lit2) n s32v)))
               s32v)
    :returns s32v
    :index n
    :last (s32v-ncols s32v))

  (local (in-theory (enable s32v-xor-lits-iter)))

  (defthm memo-tablep-s32v-xor-lits-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-xor-lits-iter n lit1 lit2 out-id s32v)))))
    :rule-classes :linear)

  (defthm memo-tablep-s32v-xor-lits-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-xor-lits-iter n lit1 lit2 out-id s32v)))))
    :rule-classes :linear)

  (defthm ncols-s32v-xor-lits-iter
    (equal (stobjs::2darr->ncols (s32v-xor-lits-iter n lit1 lit2 out-id s32v))
           (stobjs::2darr->ncols s32v)))

  (defthm len-cdr-s32v-xor-lits-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (s32v-xor-lits-iter n lit1 lit2 out-id s32v)))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm lookup-prev-in-s32v-xor-lits-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (s32v-xor-lits-iter m lit1 lit2 id
                                                              s32v))))
                    (nth slot (nth n (stobjs::2darr->rows s32v))))))

  (local (defthm bit-extend-of-b-xor
           (equal (bit-extend (b-xor a b))
                  (logxor (bit-extend a) (bit-extend b)))
           :hints(("Goal" :in-theory (enable b-xor bit-extend)))))


  (defthm lookup-in-s32v-xor-lits-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (s32v-xor-lits-iter m lit1 lit2 id s32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               (logxor (logxor (bit-extend (lit-neg lit1))
                               (s32-fix (nth slot (nth (lit-id lit1) (stobjs::2darr->rows
                                                                      s32v)))))
                       (logxor (bit-extend (lit-neg lit2))
                               (s32-fix (nth slot (nth (lit-id lit2) (stobjs::2darr->rows s32v))))))
             (nth slot (nth n (stobjs::2darr->rows s32v)))))
    :hints ((acl2::just-induct-and-expand
             (s32v-xor-lits-iter m lit1 lit2 id s32v))))


  (defthm vecsim-to-eval-of-s32v-xor-lits-iter
    (equal (vecsim-to-eval-iter n slot bit (s32v-xor-lits-iter slot1 lit1 lit2 m s32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m
                             (b-xor
                              (b-xor (lit-neg lit1)
                                     (acl2::logbit
                                      bit
                                      (s32-fix (nth slot (nth (lit-id lit1)
                                                              (stobjs::2darr->rows s32v))))))
                              (b-xor (lit-neg lit2)
                                     (acl2::logbit
                                      bit
                                      (s32-fix (nth slot (nth (lit-id lit2)
                                                              (stobjs::2darr->rows s32v)))))))
                             vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s32v vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s32v)
                       (vecsim-to-eval-iter n slot bit s32v vals
                                            aignet)))))))

(defsection s32v-zero
  (defiteration s32v-zero (out-id s32v)
    (declare (xargs :stobjs s32v
                    :guard (and (natp out-id)
                                (< out-id (s32v-nrows s32v)))))
    (s32v-set2 out-id n 0 s32v)
    :returns s32v
    :index n
    :last (s32v-ncols s32v))

  (local (in-theory (enable s32v-zero-iter)))

  (defthm memo-tablep-s32v-zero-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-zero-iter n out-id s32v)))))
    :rule-classes :linear)

  (defthm memo-tablep-s32v-zero-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (s32v-zero-iter n out-id s32v)))))
    :rule-classes :linear)

  (defthm ncols-s32v-zero-iter
    (equal (stobjs::2darr->ncols (s32v-zero-iter n out-id s32v))
           (stobjs::2darr->ncols s32v)))

  (defthm len-cdr-s32v-zero-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (s32v-zero-iter n out-id s32v)))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm lookup-prev-in-s32v-zero-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (s32v-zero-iter m id s32v))))
                    (nth slot (nth n (stobjs::2darr->rows s32v))))))

  (defthm lookup-in-s32v-zero-iter
    (equal (nth slot (nth n (stobjs::2darr->rows (s32v-zero-iter m id s32v))))
           (if (and (equal (nfix n) (nfix id))
                    (< (nfix slot) (nfix m)))
               0
             (nth slot (nth n (stobjs::2darr->rows s32v)))))
    :hints ((acl2::just-induct-and-expand
             (s32v-zero-iter m id s32v))))

  


  (defthm vecsim-to-eval-of-s32v-zero-iter
    (equal (vecsim-to-eval-iter n slot bit (s32v-zero-iter slot1 m s32v) vals aignet)
           (let ((vals (vecsim-to-eval-iter n slot bit s32v vals aignet)))
             (if (and (< (nfix m) (nfix n))
                      (< (nfix slot) (nfix slot1)))
                 (update-nth m 0 vals)
               vals)))
    :hints (("goal" :induct (vecsim-to-eval-iter n slot bit s32v
                                            vals aignet)
             :in-theory (enable (:induction vecsim-to-eval-iter))
             :expand ((:free (s32v)
                       (vecsim-to-eval-iter n slot bit s32v vals
                                            aignet)))))))

(local (in-theory (disable w)))

(defthm w-state-of-random$
  (equal (w (mv-nth 1 (random$ n state)))
         (w state))
  :hints(("Goal" :in-theory (enable random$ w read-acl2-oracle update-acl2-oracle get-global))))

(defsection s32v-randomize
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

  (defiteration s32v-randomize (out-id s32v state)
    (declare (xargs :stobjs (s32v state)
                    :guard (and (natp out-id)
                                (< out-id (s32v-nrows s32v)))
                    :guard-hints (("goal" :in-theory (enable signed-byte-p)))))
    (b* (((mv uval state) (random$ (expt 2 32) state))
         (s32v (s32v-set2 out-id n ;; (bitops::fast-logext 32 uval)
                          (- uval (expt 2 31))
                          s32v)))
      (mv s32v state))
    :returns (mv s32v state)
    :index n
    :last (s32v-ncols s32v))

  (local (in-theory (enable s32v-randomize-iter)))

  (defthm memo-tablep-s32v-randomize-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (mv-nth 0 (s32v-randomize-iter n out-id s32v state))))))
    :rule-classes :linear)

  (defthm ncols-s32v-randomize-iter
    (equal (stobjs::2darr->ncols (mv-nth 0 (s32v-randomize-iter n out-id s32v state)))
           (stobjs::2darr->ncols s32v)))

  (defthm len-cdr-s32v-randomize-iter
    (implies (< (nfix out-id) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (mv-nth 0 (s32v-randomize-iter n out-id s32v state))))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm lookup-prev-in-s32v-randomize-iter
    (implies (<= (nfix m) (nfix slot))
             (equal (nth slot (nth n (stobjs::2darr->rows (mv-nth 0 (s32v-randomize-iter m id s32v state)))))
                    (nth slot (nth n (stobjs::2darr->rows s32v))))))

  (defthm w-state-of-s32v-randomize-iter
    (equal (w (mv-nth 1 (s32v-randomize-iter m id s32v state)))
           (w state)))

  (defthm w-state-of-s32v-randomize
    (equal (w (mv-nth 1 (s32v-randomize id s32v state)))
           (w state))))


(defsection aignet-vecsim
  :parents (vector-simulation)
  :short "Simulate an AIG on N*32 parallel input vectors."
  :long "<p>This takes an @(see s32v) that has at least one row (see @(see
s32v-nrows)) for each fanin node of the AIG and is seeded with combinational
input values.  This function sweeps over the AIG to compute all other fanin
values given those inputs.  After this, the Kth bit of the Nth row of the s32v
will equal the @('id-eval') of the AIG under the inputs/registers computed by
collecting the Kth bit of the rows corresponding to input and register
nodes.</p>

<p>If you want to simulate only one 32-bit set of values at a time, it is
faster and logically equivalent to use @(see aignet-vecsim1) or @(see
aignet-vecsim-top) (which logically equals @('aignet-vecsim') but uses
@('aignet-vecsim1') when the input @('s32v') is one column wide).</p>

<p>The combinational inputs of the AIG must have values already set in the
@('s32v') before starting.  You may initialize them to random values using
@(see s32v-randomize-inputs) and @(see s32v-randomize-regs).</p>

<p>@(csee exhaustive-sim) wraps @('aignet-vecsim') and performs an exhaustive
simulation to find whether there is any input setting that results in the 0th
output producing 1; i.e. whether the 0th output is satisfiable.</p>"
  (defiteration aignet-vecsim (s32v aignet)

    (declare (xargs :stobjs (s32v aignet)
                    :guard (<= (num-fanins aignet) (s32v-nrows s32v))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode->fanin slot0))
                   (slot1 (id->slot nid 1 aignet))
                   (f1 (snode->fanin slot1)))
                (if (eql 1 (snode->regp slot1))
                    (s32v-xor-lits f0 f1 nid s32v)
                  (s32v-and-lits f0 f1 nid s32v)))
       :const (s32v-zero nid s32v)
       :in    s32v))
    :returns s32v
    :index n
    :last (num-fanins aignet)
    :package aignet::foo)

  (defthm car-nonnil-forward-to-consp
    (implies (car x)
             (consp x))
    :rule-classes :forward-chaining)

  ;; (defiteration aignet-vecsim-frame (s32v aignet)
  ;;   (declare (xargs :stobjs (s32v aignet)
  ;;                   :guard (<= (num-fanins aignet) (s32v-nrows s32v))
  ;;                   :guard-hints ((and stable-under-simplificationp
  ;;                                      '(:in-theory (enable aignet-idp))))))
  ;;   (b* ((n (lnfix n))
  ;;        (nid n)
  ;;        (slot0 (id->slot nid 0 aignet))
  ;;        (type (snode->type slot0)))
  ;;     (aignet-case
  ;;      type (id->regp nid aignet)
  ;;      :gate  (b* ((f0 (snode->fanin slot0))
  ;;                  (slot1 (id->slot nid 1 aignet))
  ;;                  (f1 (snode->fanin slot1)))
  ;;               (if (eql 1 (snode->regp slot1))
  ;;                   (s32v-xor-lits f0 f1 nid s32v)
  ;;                 (s32v-and-lits f0 f1 nid s32v)))
  ;;      :pi    s32v
  ;;      :reg   (b* ((ri (reg-id->nxst (regnum->id (ci-id->ionum nid aignet)
  ;;                                                aignet)
  ;;                                    aignet)))
  ;;               (s32v-copy-lit (mk-lit ri 0) nid s32v))
  ;;      :co    (b* ((f0 (snode->fanin slot0)))
  ;;               (s32v-copy-lit f0 nid s32v))
  ;;      :const (s32v-zero nid s32v)))
  ;;   :returns s32v
  ;;   :index n
  ;;   :last (num-fanins aignet)
  ;;   :package aignet::foo)

  (local (in-theory (enable aignet-vecsim-iter ;; aignet-vecsim-frame-iter
                            )))

  (defthm memo-tablep-aignet-vecsim-iter
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (< (fanin-count aignet) (len (stobjs::2darr->rows (aignet-vecsim-iter n s32v aignet)))))
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
             (equal (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter n s32v aignet))))
                    (nth slot (nth m (stobjs::2darr->rows s32v)))))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n s32v aignet))))

  (defthm ncols-of-aignet-vecsim-iter
    (equal (stobjs::2darr->ncols (aignet-vecsim-iter n s32v aignet))
           (stobjs::2darr->ncols s32v))
    :hints ((acl2::just-induct-and-expand (aignet-vecsim-iter n s32v aignet))))

  (defthm nrows-of-aignet-vecsim-iter
    (implies (<= n (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows (aignet-vecsim-iter n s32v aignet)))
                    (len (stobjs::2darr->rows s32v)))))

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
                         (< (nfix slot) (s32v-ncols s32v)))
                    (acl2::bit-equiv
                     (acl2::logbit bit (s32-fix (nth slot
                                                     (nth id (stobjs::2darr->rows (aignet-vecsim-iter
                                                                                   n s32v
                                                                                   aignet))))))
                     (let* ((vals
                             (vecsim-to-eval slot bit s32v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                       (id-eval id in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (e/d (lit-eval eval-and-of-lits eval-xor-of-lits)
                                          (id-eval
                                           aignet-vecsim-iter))
                   :induct (id-eval-ind id aignet)
                   :expand ((:free (in-vals reg-vals) (id-eval id in-vals reg-vals aignet))
                            (aignet-vecsim-iter (+ 1 (nfix id))
                                                s32v aignet)
                            (aignet-vecsim-iter 1 s32v aignet))))))

  (defthm aignet-vecsim-iter-correct
    (implies (and (aignet-idp m aignet)
                  (< (nfix m) (nfix n))
                  (< (nfix slot) (s32v-ncols s32v)))
             (equal (acl2::logbit bit (s32-fix (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim-iter n s32v aignet))))))
                    (let* ((vals
                             (vecsim-to-eval slot bit s32v vals
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
                  (< (nfix slot) (s32v-ncols s32v)))
             (equal (acl2::logbit bit (s32-fix (nth slot (nth m (stobjs::2darr->rows (aignet-vecsim s32v aignet))))))
                    (let* ((vals
                             (vecsim-to-eval slot bit s32v vals
                                             aignet))
                            (in-vals (aignet-vals->invals nil vals
                                                          aignet))
                            (reg-vals (aignet-vals->regvals nil vals aignet)))
                      (id-eval m in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (e/d (aignet-idp)
                                   (bitops::logbit-to-logbitp
                                    aignet-vecsim-iter)))))


  (defthm aignet-eval-iter-out-of-bounds
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-iter n vals aignet))
                    (nth m vals)))
    :hints((acl2::just-induct-and-expand
            (aignet-eval-iter n vals aignet))))

  (defthm aignet-eval-out-of-bounds
    (implies (< (fanin-count aignet) (nfix m))
             (equal (nth m (aignet-eval vals aignet))
                    (nth m vals)))
    :hints(("Goal" :in-theory (enable aignet-eval))))

  (defthm aignet-vecsim-to-eval-lemma
    (implies (< (nfix slot) (s32v-ncols s32v))
             (bit-equiv
              (nth id (vecsim-to-eval slot bit (aignet-vecsim s32v aignet) vals aignet))
              (nth id (aignet-eval (vecsim-to-eval slot bit s32v vals
                                                   aignet) aignet))))
    :hints (("goal" :in-theory (e/d (aignet-idp)
                                    (bitops::logbit-to-logbitp
                                     aignet-vecsim))
             :cases ((aignet-idp id aignet)))))

  (defthm aignet-vecsim-to-eval
    (implies (< (nfix slot) (s32v-ncols s32v))
             (bits-equiv
              (vecsim-to-eval slot bit (aignet-vecsim s32v aignet) vals aignet)
              (aignet-eval (vecsim-to-eval slot bit s32v vals aignet) aignet)))
    :hints (("goal" :in-theory (disable aignet-vecsim))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(defsection aignet-vecsim1
  :parents (vector-simulation)
  :short "Simulate an AIG on 32 parallel input vectors."
  (defiteration aignet-vecsim1 (s32v aignet)
    (declare (xargs :stobjs (s32v aignet)
                    :guard (and (<= (num-fanins aignet) (s32v-nrows s32v))
                                (equal (s32v-ncols s32v) 1))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
        type
        :gate  (b* ((f0 (snode->fanin slot0))
                    (slot1 (id->slot nid 1 aignet))
                    (f1 (snode->fanin slot1)))
                 (s32v-set n
                           (if (eql 1 (snode->regp slot1))
                               (logxor (bit-extend (b-xor (lit->neg f0) (lit->neg f1)))
                                       (s32v-get (lit->var f0) s32v)
                                       (s32v-get (lit->var f1) s32v))
                             (logand (logxor (bit-extend (lit->neg f0))
                                             (s32v-get (lit->var f0) s32v))
                                     (logxor (bit-extend (lit->neg f1))
                                             (s32v-get (lit->var f1) s32v))))
                           s32v))
        :const (s32v-set n 0 s32v)
        :in    s32v))
    :returns s32v
    :index n
    :last (num-fanins aignet)
    :package aignet::foo)

  (local (in-theory (enable aignet-vecsim-iter)))

  (local (in-theory (disable s32vl-get2 s32vl-set2)))

  (local (defthm floor-1
           (implies (natp x)
                    (equal (floor x 1) x))
           :hints(("Goal" :in-theory (enable floor)))))

  (local (defthm 2darr-index-inverse-when-ncols-is-1
           (equal (stobjs::2darr-index-inverse idx nrows 1)
                  (mv (nfix idx) 0))
           :hints(("Goal" :in-theory (enable stobjs::2darr-index-inverse mod)))))
  
  (local (defthm bit-extend-of-b-xor
           (equal (bit-extend (b-xor a b))
                  (logxor (bit-extend a) (bit-extend b)))
           :hints(("Goal" :in-theory (enable b-xor bit-extend)))))

  (defthm aignet-vecsim1-iter-is-aignet-vecsim-iter
    (implies (equal (s32v-ncols s32v) 1)
             (equal (aignet-vecsim1-iter n s32v aignet)
                    (aignet-vecsim-iter n s32v aignet)))
    :hints(("Goal" :induct t
            :expand ((:free (lit0 lit1 n s32v) (s32v-and-lits-iter 1 lit0 lit1 n s32v))
                     (:free (lit0 lit1 n s32v) (s32v-and-lits-iter 0 lit0 lit1 n s32v))
                     (:free (lit0 lit1 n s32v) (s32v-xor-lits-iter 1 lit0 lit1 n s32v))
                     (:free (lit0 lit1 n s32v) (s32v-xor-lits-iter 0 lit0 lit1 n s32v))
                     (:free (lit0 n s32v) (s32v-copy-lit-iter 1 lit0 n s32v))
                     (:free (lit0 n s32v) (s32v-copy-lit-iter 0 lit0 n s32v))
                     (:free (n s32v) (s32v-zero-iter 1 n s32v))
                     (:free (n s32v) (s32v-zero-iter 0 n s32v))
                     (aignet-vecsim1-iter n s32v aignet)
                    (aignet-vecsim-iter n s32v aignet)))))

  (defthm aignet-vecsim1-is-aignet-vecsim
    (implies (equal (s32v-ncols s32v) 1)
             (equal (aignet-vecsim1 s32v aignet)
                    (aignet-vecsim s32v aignet)))))

(define aignet-vecsim-top (s32v aignet)
  :enabled t
  :guard (<= (num-fanins aignet) (s32v-nrows s32v))
  :parents (vector-simulation)
  :short "Logically same as @(see aignet-vecsim), but optimizes by calling
@(see aignet-vecsim1) when s32v has only 1 column"
  (mbe :logic (aignet-vecsim s32v aignet)
       :exec (if (eql (s32v-ncols s32v) 1)
                 (aignet-vecsim1 s32v aignet)
               (aignet-vecsim s32v aignet))))






;; (defsection aignet-vecsim1
;;   (defiteration aignet-vecsim1 (s32v aignet)
;;     (declare (xargs :stobjs (s32v aignet)
;;                     :guard (and (<= (+ 1 (max-fanin aignet)) (s32v-nrows s32v))
;;                                 (equal (s32v-ncols s32v) 1))
;;                     :guard-hints (("goal" :in-theory (enable aignet-idp)))))
;;     (b* ((n (lnfix n))
;;          (nid n)
;;          (slot0 (id->slot nid 0 aignet))
;;          (type (snode->type slot0)))
;;       (aignet-case
;;         type
;;         :gate  (b* ((f0 (snode->fanin slot0))
;;                     (slot1 (id->slot nid 1 aignet))
;;                     (f1 (snode->fanin slot1)))
;;                  (s32v-set n
;;                            (if (eql 1 (snode->regp slot1))
;;                                (logxor (bit-extend (b-xor (lit->neg f0) (lit->neg f1)))
;;                                        (s32v-get (lit->var f0) s32v)
;;                                        (s32v-get (lit->var f1) s32v))
;;                              (logand (logxor (bit-extend (lit->neg f0))
;;                                              (s32v-get (lit->var f0) s32v))
;;                                      (logxor (bit-extend (lit->neg f1))
;;                                              (s32v-get (lit->var f1) s32v))))
;;                            s32v))
;;         :out   s32v
;;         :const (s32v-set n 0 s32v)
;;         :in    s32v))
;;     :returns s32v
;;     :index n
;;     :last (+ 1 (max-fanin aignet))
;;     :package aignet::foo)

;;   (local (in-theory (enable aignet-vecsim-iter)))

;;   (local (in-theory (disable s32vl-get2 s32vl-set2)))

;;   (local (defthm floor-1
;;            (implies (natp x)
;;                     (equal (floor x 1) x))
;;            :hints(("Goal" :in-theory (enable floor)))))

;;   (local (defthm 2darr-index-inverse-when-ncols-is-1
;;            (equal (stobjs::2darr-index-inverse idx nrows 1)
;;                   (mv (nfix idx) 0))
;;            :hints(("Goal" :in-theory (enable stobjs::2darr-index-inverse mod)))))
  
;;   (local (defthm bit-extend-of-b-xor
;;            (equal (bit-extend (b-xor a b))
;;                   (logxor (bit-extend a) (bit-extend b)))
;;            :hints(("Goal" :in-theory (enable b-xor bit-extend)))))

;;   (defthm aignet-vecsim1-iter-is-aignet-vecsim-iter
;;     (implies (equal (s32v-ncols s32v) 1)
;;              (equal (aignet-vecsim1-iter n s32v aignet)
;;                     (aignet-vecsim-iter n s32v aignet)))
;;     :hints(("Goal" :induct t
;;             :expand ((:free (lit0 lit1 n s32v) (s32v-and-lits-iter 1 lit0 lit1 n s32v))
;;                      (:free (lit0 lit1 n s32v) (s32v-and-lits-iter 0 lit0 lit1 n s32v))
;;                      (:free (lit0 lit1 n s32v) (s32v-xor-lits-iter 1 lit0 lit1 n s32v))
;;                      (:free (lit0 lit1 n s32v) (s32v-xor-lits-iter 0 lit0 lit1 n s32v))
;;                      (:free (lit0 n s32v) (s32v-copy-lit-iter 1 lit0 n s32v))
;;                      (:free (lit0 n s32v) (s32v-copy-lit-iter 0 lit0 n s32v))
;;                      (:free (n s32v) (s32v-zero-iter 1 n s32v))
;;                      (:free (n s32v) (s32v-zero-iter 0 n s32v))
;;                      (aignet-vecsim1-iter n s32v aignet)
;;                     (aignet-vecsim-iter n s32v aignet)))))

;;   (defthm aignet-vecsim1-is-aignet-vecsim
;;     (implies (equal (s32v-ncols s32v) 1)
;;              (equal (aignet-vecsim1 s32v aignet)
;;                     (aignet-vecsim s32v aignet)))))


;; (define aignet-vecsim-top (s32v aignet)
;;   :enabled t
;;   :guard (<= (+ 1 (max-fanin aignet)) (s32v-nrows s32v))
;;   (mbe :logic (aignet-vecsim s32v aignet)
;;        :exec (if (eql (s32v-ncols s32v) 1)
;;                  (aignet-vecsim1 s32v aignet)
;;                (aignet-vecsim s32v aignet))))




(define s32v-randomize-inputs ((n natp "start at 0")
                               (s32v)
                               (aignet)
                               (state))
  :parents (vector-simulation)
  :short "Assign random values to the PI nodes of an AIG in an @(see s32v)"
  :guard (and (<= n (num-ins aignet))
              (<= (num-fanins aignet) (s32v-nrows s32v)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :returns (mv new-s32v new-state)
  (if (mbe :logic (zp (- (num-ins aignet) (nfix n)))
           :exec (eql n (num-ins aignet)))
      (mv s32v state)
    (b* (((mv s32v state) (s32v-randomize (innum->id n aignet) s32v state)))
      (s32v-randomize-inputs (1+ (lnfix n)) s32v aignet state)))
  ///
  (defret ncols-of-s32v-randomize-inputs
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v)))

  (defret nrows-of-s32v-randomize-inputs
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defret w-state-of-s32v-randomize-inputs
    (equal (w new-state)
           (w state))))

(define s32v-randomize-regs ((n natp "start at 0")
                             (s32v)
                             (aignet)
                             (state))
  :parents (vector-simulation)
  :short "Assign random values to the register nodes of an AIG in an @(see s32v)"
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (s32v-nrows s32v)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (mv new-s32v new-state)
  (if (mbe :logic (zp (- (num-regs aignet) (nfix n)))
           :exec (eql n (num-regs aignet)))
      (mv s32v state)
    (b* (((mv s32v state) (s32v-randomize (regnum->id n aignet) s32v state)))
      (s32v-randomize-regs (1+ (lnfix n)) s32v aignet state)))
  ///
  (defret ncols-of-s32v-randomize-regs
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v)))

  (defret nrows-of-s32v-randomize-regs
    (implies (< (fanin-count aignet) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defthm w-state-of-s32v-randomize-regs
    (equal (w (mv-nth 1 (s32v-randomize-regs n s32v aignet state)))
           (w state))
    :hints(("Goal" :in-theory (enable s32v-randomize-regs)))))
  
  





(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable acl2::nth-when-zp)))



(local (defthm pi-count-<=-fanin-count
         (<= (stype-count :pi aignet)
             (fanin-count aignet))
         :hints(("Goal" :in-theory (enable stype-count fanin-count)))
         :rule-classes :linear))

(local (in-theory (disable nth update-nth)))

(local (defthm 2darr-index-inverse-when-1-col
         (equal (stobjs::2darr-index-inverse idx nrows 1)
                (mv (nfix idx) 0))
         :hints(("Goal" :in-theory (enable stobjs::2darr-index-inverse
                                           floor mod)))))

(define int-to-bitlist ((width natp) (x integerp))
  :returns (bitlist bit-listp)
  (if (zp width)
      nil
    (cons (logcar x) (int-to-bitlist (1- width) (logcdr x))))
  ///
  (local (defun nth-of-int-to-bitlist-ind (n width x)
           (if (zp n)
               (list width x)
             (nth-of-int-to-bitlist-ind (1- n) (1- width) (logcdr x)))))
  (defret nth-of-<fn>
    (bit-equiv (nth n bitlist)
               (logbit n (loghead width x)))
    :hints(("Goal" 
            :induct (nth-of-int-to-bitlist-ind n width x)
            :expand ((:free (x) (nth n x))
                     (:free (x) (logbitp n x))
                     (loghead width x)
                     <call>)))))


(define bitlist-to-nat ((x bit-listp))
  :returns (val natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (logcons (car x)
             (bitlist-to-nat (cdr x))))
  ///
  (defret logbitp-of-<fn>
    (equal (logbitp n val)
           (bit->bool (nth n x)))
    :hints(("Goal" :in-theory (enable bitops::logbitp** nth)
            :induct (nth n x))))

  (defret <fn>-of-int-to-bitlist
    :pre-bind ((x (int-to-bitlist width in)))
    (equal val (loghead width in))
    :hints ((bitops::logbitp-reasoning)))
  
  (defret int-to-bitlist-of-<fn>
    (bits-equiv (int-to-bitlist width val)
                (take width x))
    :hints(("Goal" :in-theory (enable bits-equiv
                                      bitops::logbitp-of-loghead-split)))))

(local (defthm nth-of-aignet-invals->vals-tailrec
         (implies (natp start)
                  (equal (nth n (aignet-invals->vals-tailrec start invals vals aignet))
                         (b* ((suffix (lookup-id n aignet))
                              (innum (stype-count :pi (cdr suffix))))
                           (if (and (equal (stype (car suffix)) :pi)
                                    (<= (ifix start) innum))
                               (bfix (nth innum invals))
                             (nth n vals)))))
         :hints(("Goal" :in-theory (enable* aignet-invals->vals-tailrec
                                            arith-equiv-forwarding)))))

(define exhaustive-sim-generate-inputs-aux ((input-val :type (unsigned-byte 32))
                                  (input-idx :type (unsigned-byte 32))
                                  s32v aignet)
  :guard (and (equal (s32v-ncols s32v) 1)
              (<= 5 input-idx)
              (<= input-idx (num-ins aignet))
              (<= (num-fanins aignet) (s32v-nrows s32v))
              (< (num-fanins aignet) (expt 2 32)))
  :measure (nfix (- (num-ins aignet) (nfix input-idx)))
  :returns (new-s32v)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable unsigned-byte-p))))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix input-idx)))
                   :exec (eql (num-ins aignet) input-idx)))
        s32v)
       (id (innum->id input-idx aignet))
       (val (bit-extend (logbit (- (lnfix input-idx) 5) input-val)))
       (s32v (s32v-set id val s32v)))
    (exhaustive-sim-generate-inputs-aux input-val (1+ (lnfix input-idx)) s32v aignet))
  ///
  (defret nrows-of-<fn>
    (implies (and (<= (num-fanins aignet) (s32v-nrows s32v))
                  (equal (s32v-ncols s32v) 1))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (s32v-nrows s32v)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (disable (:d <fn>)))))

  (defret ncols-of-<fn>
    (equal (stobjs::2darr->ncols new-s32v)
           (s32v-ncols s32v))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (disable (:d <fn>)))))

  (defret nth-of-<fn>
    (implies (equal (stobjs::2darr->ncols s32v) 1)
             (equal (nth 0 (nth n (stobjs::2darr->rows new-s32v)))
                    (b* ((suffix (lookup-id n aignet))
                         (innum (stype-count :pi (cdr suffix))))
                      (if (and (equal (stype (car suffix)) :pi)
                               (<= (nfix input-idx) innum))
                          (bit-extend (logbit (- innum 5) input-val))
                        (nth 0 (nth n (stobjs::2darr->rows s32v))))))))

  (defret nth-vecsim-to-eval-of-<fn>
    (implies (equal (stobjs::2darr->ncols s32v) 1)
             (equal (nth n (vecsim-to-eval 0 bit new-s32v vals aignet))
                    (b* ((suffix (lookup-id n aignet))
                         (innum (stype-count :pi (cdr suffix))))
                      (if (and (equal (stype (car suffix)) :pi)
                               (<= (nfix input-idx) innum))
                          (logbit (- innum 5) input-val)
                        (nth n (vecsim-to-eval 0 bit s32v vals aignet))))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable <fn>))))
  
  

  (defret vecsim-to-eval-of-<fn>
    (implies (and (equal (stobjs::2darr->ncols s32v) 1)
                  (<= 5 (nfix input-idx))
                  (bind-free '((low-5-bits . '0)) (low-5-bits)))
             (bits-equiv (vecsim-to-eval 0 bit new-s32v vals aignet)
                         (aignet-invals->vals-tailrec (nfix input-idx)
                                                      (int-to-bitlist (num-ins aignet)
                                                                      (logapp 5 low-5-bits input-val))
                                                      (vecsim-to-eval 0 bit s32v vals aignet)
                                                      aignet)))
    :hints(("Goal" :in-theory (enable bits-equiv)
            :do-not-induct t))))
               
               


(local (defthm len-of-update-nth-preserved
         (implies (< (nfix n) (len x))
                  (equal (len (update-nth n v x))
                         (len x)))))

(define exhaustive-sim-generate-inputs ((input-val :type (unsigned-byte 32))
                              s32v aignet)
  :guard (and (equal (s32v-ncols s32v) 1)
              (<= (num-fanins aignet) (s32v-nrows s32v))
              (< (num-fanins aignet) (expt 2 32)))
  :returns (new-s32v)
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable unsigned-byte-p))))
  :guard-hints (("goal" :in-theory (disable  acl2::len-of-update-nth
                                             len-update-nth
                                             acl2::update-nth-of-nth-free
                                             nth-update-nth)))
  (b* (((when (<= (num-ins aignet) 0)) s32v)
       (s32v (s32v-set (innum->id 0 aignet) (logext 32 #uxaaaa_aaaa) s32v))
       ((when (<= (num-ins aignet) 1)) s32v)
       (s32v (s32v-set (innum->id 1 aignet) (logext 32 #uxcccc_cccc) s32v))
       ((when (<= (num-ins aignet) 2)) s32v)
       (s32v (s32v-set (innum->id 2 aignet) (logext 32 #uxf0f0_f0f0) s32v))
       ((when (<= (num-ins aignet) 3)) s32v)
       (s32v (s32v-set (innum->id 3 aignet) (logext 32 #uxff00_ff00) s32v))
       ((when (<= (num-ins aignet) 4)) s32v)
       (s32v (s32v-set (innum->id 4 aignet) (logext 32 #uxffff_0000) s32v)))
    (exhaustive-sim-generate-inputs-aux input-val 5 s32v aignet))
  ///
  (defret nrows-of-<fn>
    (implies (and (<= (num-fanins aignet) (s32v-nrows s32v))
                  (equal (s32v-ncols s32v) 1))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (s32v-nrows s32v))))

  (defret ncols-of-<fn>
    (equal (stobjs::2darr->ncols new-s32v)
           (s32v-ncols s32v))
    :hints(("Goal" :in-theory (disable acl2::len-of-update-nth
                                       len-update-nth
                                       acl2::update-nth-of-nth-free
                                       nth-update-nth))))

  
  (defret nth-of-<fn>
    (implies (equal (stobjs::2darr->ncols s32v) 1)
             (equal (nth 0 (nth n (stobjs::2darr->rows new-s32v)))
                    (b* ((suffix (lookup-id n aignet))
                         (innum (stype-count :pi (cdr suffix))))
                      (if (equal (stype (car suffix)) :pi)
                          (case innum
                            (0 (logext 32 #uxaaaa_aaaa))
                            (1 (logext 32 #uxcccc_cccc))
                            (2 (logext 32 #uxf0f0_f0f0))
                            (3 (logext 32 #uxff00_ff00))
                            (4 (logext 32 #uxffff_0000))
                            (t (bit-extend (logbit (- innum 5) input-val))))
                        (nth 0 (nth n (stobjs::2darr->rows s32v))))))))

  (local (in-theory (disable bitops::logbitp-of-negative-const)))

  (local (defun characterize-logbitp-of-mask (n mask idx)
           (b* (((when (zp n)) t)
                (bit (1- n))
                ((unless (eql (logbitp bit mask)
                              (logbitp idx bit)))
                 nil))
             (characterize-logbitp-of-mask (1- n) mask idx))))

  (local (defthm characterize-logbitp-of-mask-correct
           (implies (and (natp bit)
                         (< bit (nfix n))
                         (not (equal (logbitp bit mask)
                                     (logbitp idx bit))))
                    (not (characterize-logbitp-of-mask n mask idx)))))
             
  
  (local (defthm logbitp-of-aaaa_aaaa
           (implies (< (nfix bit) 32)
                    (Equal (logbitp bit #uxaaaa_aaaa)
                           (logbitp 0 (nfix bit))))
           :hints (("goal" :use ((:instance characterize-logbitp-of-mask-correct
                                  (bit (nfix bit)) (n 32) (mask #uxaaaa_aaaa) (idx 0)))))))

  (local (defthm logbitp-of-cccc_cccc
           (implies (< (nfix bit) 32)
                    (Equal (logbitp bit #uxcccc_cccc)
                           (logbitp 1 (nfix bit))))
           :hints (("goal" :use ((:instance characterize-logbitp-of-mask-correct
                                  (bit (nfix bit)) (n 32) (mask #uxcccc_cccc) (idx 1)))))))

  (local (defthm logbitp-of-f0f0_f0f0
           (implies (< (nfix bit) 32)
                    (Equal (logbitp bit #uxf0f0_f0f0)
                           (logbitp 2 (nfix bit))))
           :hints (("goal" :use ((:instance characterize-logbitp-of-mask-correct
                                  (bit (nfix bit)) (n 32) (mask #uxf0f0_f0f0) (idx 2)))))))

  (local (defthm logbitp-of-ff00_ff00
           (implies (< (nfix bit) 32)
                    (Equal (logbitp bit #uxff00_ff00)
                           (logbitp 3 (nfix bit))))
           :hints (("goal" :use ((:instance characterize-logbitp-of-mask-correct
                                  (bit (nfix bit)) (n 32) (mask #uxff00_ff00) (idx 3)))))))

  (local (defthm logbitp-of-ffff_0000
           (implies (< (nfix bit) 32)
                    (Equal (logbitp bit #uxffff_0000)
                           (logbitp 4 (nfix bit))))
           :hints (("goal" :use ((:instance characterize-logbitp-of-mask-correct
                                  (bit (nfix bit)) (n 32) (mask #uxffff_0000) (idx 4)))))))

  
  (local (in-theory (disable (logext))))

  (defret nth-vecsim-to-eval-of-<fn>
    (implies (and (equal (stobjs::2darr->ncols s32v) 1)
                  (< (nfix bit) 32))
             (equal (nth n (vecsim-to-eval 0 bit new-s32v vals aignet))
                    (b* ((suffix (lookup-id n aignet))
                         (innum (stype-count :pi (cdr suffix))))
                      (if (equal (stype (car suffix)) :pi)
                          (if (< innum 5)
                              (logbit innum (nfix bit))
                            (logbit (- innum 5) input-val))
                        (nth n (vecsim-to-eval 0 bit s32v vals aignet))))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable <fn>))))


  (local (defthm stype-when-stype-count-0
           (implies (and (equal (stype-count stype aignet) 0)
                         (not (equal stype :const)))
                    (not (equal (stype (car (lookup-id n aignet))) stype)))
           :hints(("Goal" :in-theory (enable lookup-id stype-count)))))

  (local (defret vecsim-to-eval-of-<fn>-lemma
           (implies (and (equal (stobjs::2darr->ncols s32v) 1)
                         (< (nfix bit) 32))
                    (bits-equiv (vecsim-to-eval 0 bit new-s32v vals aignet)
                                (aignet-invals->vals-tailrec
                                 0
                                 (int-to-bitlist (num-ins aignet)
                                                 (logapp 5 (nfix bit) input-val))
                                 (vecsim-to-eval 0 bit s32v vals aignet)
                                 aignet)))
           :hints(("Goal"
                   :in-theory (e/d (bits-equiv)
                                   (aignet-invals->vals-tailrec-is-aignet-invals->vals-iter
                                    <fn>))))))

  (defret vecsim-to-eval-of-<fn>
    (implies (and (equal (stobjs::2darr->ncols s32v) 1)
                  (< (nfix bit) 32))
             (bits-equiv (vecsim-to-eval 0 bit new-s32v vals aignet)
                         (aignet-invals->vals
                          (int-to-bitlist (num-ins aignet)
                                          (logapp 5 (nfix bit) input-val))
                          (vecsim-to-eval 0 bit s32v vals aignet)
                          aignet)))
    :hints(("Goal" :use vecsim-to-eval-of-<fn>-lemma
            :in-theory (e/d (aignet-invals->vals)
                            (<fn>))))))



       

(define logbitp-witness ((x integerp))
  :guard (not (equal x 0))
  :returns (idx natp :rule-classes :type-prescription
                :hints (("goal" :expand ((integer-length x)))))
  (if (< (lifix x) 0)
      (integer-length x)
    (mbe :logic (if (zip x)
                    0
                  (1- (integer-length x)))
         :exec (1- (integer-length x))))
  ///
  (defret logbitp-witness-bound
    (<= idx (integer-length x))
    :rule-classes ((:linear :trigger-terms ((logbitp-witness x)))))

  (defret logbitp-of-logbitp-witness
    (implies (not (zip x))
             (logbitp idx x))
    :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions)
            :induct (integer-length x)
            :expand ((integer-length x)
                     (:free (n) (logbitp n x))))
           (and stable-under-simplificationp
                '(:expand ((integer-length (logcdr x))))))))




(define exhaustive-sim-aux ((input-val :type (unsigned-byte 32))
                            (max :type (unsigned-byte 32))
                            s32v aignet)
  :guard (and ;; (<= (num-ins aignet) 32)
          (equal (s32v-ncols s32v) 1)
          (<= (num-fanins aignet) (s32v-nrows s32v))
          (< (num-fanins aignet) (expt 2 32))
          (<= input-val max)
          (<= 1 (num-outs aignet)))
  :measure (nfix (- (nfix max) (nfix input-val)))
  :returns (mv (ctrex-val acl2::maybe-natp :rule-classes :type-prescription)
               new-s32v)
  (b* ((s32v (exhaustive-sim-generate-inputs (lnfix input-val) s32v aignet))
       (s32v (aignet-vecsim-top s32v aignet))
       (output-lit (outnum->fanin 0 aignet))
       (output-val (logxor (bit-extend (lit->neg output-lit))
                           (s32v-get (lit->var output-lit) s32v)))
       ((unless (eql output-val 0))
        (mv (logapp 5 (logbitp-witness output-val) (lnfix input-val))
            s32v))
       ((when (mbe :logic (zp (- (nfix max) (nfix input-val)))
                   :exec (eql max input-val)))
        (mv nil s32v)))
    (exhaustive-sim-aux (1+ (lnfix input-val)) max s32v aignet))
  ///

  (local (defthm loghead-5-less-than-32
           (< (loghead 5 x) 32)
           :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                                  (size1 5) (size 5) (i x)))
                    :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-loghead))))))

  (local (defthm aignet-vals->regvals-when-no-regs
           (implies (equal (num-regs aignet) 0)
                    (equal (aignet-vals->regvals regvals vals aignet)
                           regvals))
           :hints(("Goal" :in-theory (enable aignet-vals->regvals
                                             aignet-vals->regvals-iter)))))

  (local (defthm id-eval-normalize-when-no-regs
           (implies (and (syntaxp (not (equal regvals ''nil)))
                         (equal (num-regs aignet) 0))
                    (equal (id-eval id invals regvals aignet)
                           (id-eval id invals nil aignet)))
           :hints (("goal" :use ((:instance id-eval-of-take-num-regs
                                  (n 0)))))))
                    

  ;; (local (defthm int-to-bitlist-lemma
  ;;          (equal (int-to-bitlist count (logapp n head tail))

  (local (defthm logapp-of-logtail-free
           (implies (equal y (logtail n x))
                    (equal (logapp n x y) (ifix x)))))
  
  (defret exhaustive-sim-aux-correct
    (implies (and (equal (output-eval 0 invals regvals aignet) 1)
                  (equal (num-regs aignet) 0)
                  (equal (s32v-ncols s32v) 1)
                  (<= (logtail 5 (bitlist-to-nat invals)) (nfix max))
                  (<= (nfix input-val) (logtail 5 (bitlist-to-nat invals))))
             ctrex-val)
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-vecsim-iter-correct
                          (m (LIT->VAR (FANIN 0 (LOOKUP-STYPE 0 :PO AIGNET))))
                          (s32v (EXHAUSTIVE-SIM-GENERATE-INPUTS (nfix INPUT-VAL) S32V AIGNET))
                          (slot 0)
                          (bit (loghead 5 (bitlist-to-nat invals)))
                          (n (num-fanins aignet))))
                   :in-theory (e/d (lit-eval output-eval)
                                   (aignet-vecsim-iter-correct))))))

  (local (defthm bitlist-to-nat-of-take-nil
           (equal (bitlist-to-nat (take n nil))
                  0)
           :hints(("Goal" :in-theory (enable bitlist-to-nat)))))
  
  (local (defthm bitlist-to-nat-of-take
           (equal (bitlist-to-nat (take n x))
                  (loghead n (bitlist-to-nat x)))
           :hints(("Goal" :in-theory (enable bitlist-to-nat
                                             bitops::loghead**)))))


  (local (defthm ash-n-gt-loghead-n
           (< (loghead n x) (ash 1 (nfix n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm ash-n-minus-1-gte-loghead-n
           (<= (loghead n x) (+ -1 (ash 1 (nfix n))))
           :hints (("goal" :use ash-n-gt-loghead-n
                    :in-theory (disable ash-n-gt-loghead-n)))))

  (local (defthm ash-1-posp
           (implies (natp n)
                    (posp (ash 1 n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))


  
  (defret exhaustive-sim-aux-exhaustive
    :pre-bind ((max (logmask (- (stype-count :pi aignet) 5)))
               (input-val 0))
    (implies (and (equal (output-eval 0 invals regvals aignet) 1)
                  (equal (num-regs aignet) 0)
                  (equal (s32v-ncols s32v) 1))
             ctrex-val)
    :hints (("goal" :use ((:instance exhaustive-sim-aux-correct
                           (invals (take (num-ins aignet) invals))
                           (max (1- (ash 1 (nfix (- (num-ins aignet) 5)))))
                           (input-val 0)))
             :in-theory (e/d (logmask output-eval bitops::expt-2-is-ash)
                             (<fn>))))))



(local (defthm len-of-resize-list
         (equal (len (resize-list lst n val))
                (nfix n))
         :hints(("Goal" :in-theory (enable resize-list)))))


(local (in-theory (disable unsigned-byte-p)))

(local (defthm unsigned-byte-p-of-logmask-strong
         (implies (and (integerp w)
                       (<= (nfix n) w))
                  (unsigned-byte-p w (logmask n)))
         :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs)
                                         (logmask))))))

(local (in-theory (disable logmask)))

(local (defthm <-of-nfix
         (implies (and (integerp y)
                       (natp x))
                  (equal (< x (nfix y))
                         (< x y)))
         :hints(("Goal" :in-theory (enable nfix)))))

(define exhaustive-sim (aignet)
  :returns (ctrex acl2::maybe-natp :rule-classes :type-prescription)
  :guard (and (<= (num-ins aignet) 37)
              (<= 1 (num-outs aignet)))
  :parents (vector-simulation)
  :short "Exhaustively simulate an AIG with one output node to determine if it is satisfiable"
  :long "<p>Given a combinational AIG with 37 or fewer inputs and no registers,
this uses @(see aignet-vecsim) to run through all combinations of inputs to
check the satisfiability of the 0th output of the AIG.  This function returns
NIL if that output is unsatisfiable (always 0), and otherwise returns a natural
number giving the satisfying assignment for the PIs; i.e. @('(logbitp n
result)') gives the assignment for input n.</p>"
  (b* (((acl2::local-stobjs s32v)
        (mv ctrex s32v))
       (s32v (s32v-resize-cols 1 s32v))
       (s32v (s32v-resize-rows (num-fanins aignet) s32v)))
    (exhaustive-sim-aux 0 (logmask (nfix (- (num-ins aignet) 5))) s32v aignet))
  ///
  (defret exhaustive-sim-correct
    (implies (and (equal (output-eval 0 invals regvals aignet) 1)
                  (equal (num-regs aignet) 0))
             ctrex)))


(define random-sim-aux ((num-sims natp)
                        invals
                        s32v aignet state)
  :guard (and ;; (<= (num-ins aignet) 32)
          (equal (s32v-ncols s32v) 1)
          (<= 1 (num-outs aignet))
          (<= (num-fanins aignet) (s32v-nrows s32v))
          (< (num-fanins aignet) (expt 2 32)))
  :guard-debug t
  :measure (nfix num-sims)
  :returns (mv ctrexp
               new-invals
               new-s32v new-state)
  (b* (((when (zp num-sims)) (mv nil invals s32v state))
       ((mv s32v state) (s32v-randomize-inputs 0 s32v aignet state))
       (s32v (aignet-vecsim-top s32v aignet))
       (output-lit (outnum->fanin 0 aignet))
       (output-val (logxor (bit-extend (lit->neg output-lit))
                           (s32v-get (lit->var output-lit) s32v)))
       ((unless (eql output-val 0))
        (b* (((acl2::local-stobjs vals)
              (mv ctrexp invals s32v state vals))
             (vals (resize-bits (num-fanins aignet) vals))
             (vals (vecsim-to-eval 0 (logbitp-witness output-val) s32v vals aignet))
             (invals (resize-bits (num-ins aignet) invals))
             (invals (aignet-vals->invals invals vals aignet)))
          (mv t invals s32v state vals))))
    (random-sim-aux (1- num-sims) invals s32v aignet state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(define random-sim ((num-sims natp)
                    (invals "counterexample written here")
                    aignet state)
  :returns (mv ctrexp invals
               new-state)
  :guard (<= 1 (num-outs aignet))
  :parents (vector-simulation)
  :short "Exhaustively simulate an AIG with one output node to determine if it is satisfiable"
  :long "<p>Given a combinational AIG with 37 or fewer inputs and no registers,
this uses @(see aignet-vecsim) to run through all combinations of inputs to
check the satisfiability of the 0th output of the AIG.  This function returns
NIL if that output is unsatisfiable (always 0), and otherwise returns a natural
number giving the satisfying assignment for the PIs; i.e. @('(logbitp n
result)') gives the assignment for input n.</p>"
  (b* (((acl2::local-stobjs s32v)
        (mv ctrexp invals s32v state))
       (s32v (s32v-resize-cols 1 s32v))
       (s32v (s32v-resize-rows (num-fanins aignet) s32v)))
    (random-sim-aux num-sims invals s32v aignet state))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



