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

(in-package "AIGNET")

(include-book "centaur/aignet/vecsim" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(include-book "centaur/misc/s32-listp" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable nth update-nth)))
(local (include-book "centaur/fty/fixequiv" :dir :system))
(local (std::add-default-post-define-hook :fix))
;; Each node has a next and a head.  The head is the lowest-numbered node in
;; the equiv class.  The next is the next-higher-numbered node in the equiv
;; class.  If next<=node, the node is the last in its class.
;; If head >= node, the node is first in its class and head is the last.
;; So head == node indicates a singleton class.
(defstobj classes
  (class-nexts :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (class-heads :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  :inline t)

(define classes-size (classes)
  (min (class-nexts-length classes)
       (class-heads-length classes)))

;; (define classes-sized ((size natp) classes)
;;   (and (<= (lnfix size) (class-nexts-length classes))
;;        (<= (lnfix size) (class-heads-length classes)))
;;   ///
;;   (defthm classes-sized-when-greater
;;     (implies (and (classes-sized size2 classes)
;;                   (<= (nfix size1) (nfix size2)))
;;              (classes-sized size1 classes))))


(local (defthm class-nextsp-is-u32-listp
         (equal (class-nextsp x)
                (acl2::u32-listp x))))

(local (defthm class-headsp-is-u32-listp
         (equal (class-headsp x)
                (acl2::u32-listp x))))

(local (defthm natp-nth-in-u32-listp
         (implies (and (acl2::u32-listp x)
                       (< (nfix n) (len x)))
                  (and (natp (nth n x))
                       (integerp (nth n x))
                       (<= 0 (nth n x))))))

(local (in-theory (disable class-nextsp class-headsp acl2::u32-listp)))

(define node-next ((node natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :inline t
  (lnfix (class-nextsi node classes)))

(define node-head ((node natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :inline t
  (lnfix (class-headsi node classes)))

(define classes-wellformed-aux ((n natp)
                                classes)
  :guard (<= n (classes-size classes))
  :measure (nfix n)
  (if (zp n)
      t
    (and (< (node-next (1- n) classes) (classes-size classes))
         (< (node-head (1- n) classes) (classes-size classes))
         (classes-wellformed-aux (1- n) classes)))
  ///
  (defthmd classes-wellformed-aux-implies
    (implies (and (classes-wellformed-aux n classes)
                  (< (nfix m) (nfix n)))
             (and (< (node-next m classes) (classes-size classes))
                  (< (node-head m classes) (classes-size classes))))
    :hints (("goal" :induct (classes-wellformed-aux n classes))
            (and stable-under-simplificationp
                 '(:expand ((classes-wellformed-aux (nfix m) classes)))))))

(define classes-wellformed (classes)
  (classes-wellformed-aux (classes-size classes) classes)
  ///
  (defthm classes-wellformed-implies
    (implies (and (classes-wellformed classes)
                  (< (nfix m) (classes-size classes)))
             (and (< (node-next m classes) (classes-size classes))
                  (< (node-head m classes) (classes-size classes))))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux-implies)))
    :rule-classes (:rewrite :linear)))



(define node-set-next ((node natp) (next natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :returns (new-classes)
  (mbe :logic (update-class-nextsi node (nfix next) classes)
       :exec (if (< next (ash 1 32))
                 (update-class-nextsi node next classes)
               (non-exec (update-class-nextsi node next classes))))
  ///
  (std::defret classes-size-of-node-set-next
    (<= (classes-size classes)
        (classes-size new-classes))
    :hints(("Goal" :in-theory (enable classes-size)))
    :rule-classes :linear)

  (std::defret classes-size-of-node-set-next-equal
    (implies (< (nfix node) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes)))
    :hints(("Goal" :in-theory (enable classes-size))))

  (std::defret node-set-next-preserves-wellformed-aux
    (implies (and (< (nfix next) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed-aux n classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux classes-size node-next node-head)
            :induct (classes-wellformed-aux n classes))))

  (std::defret node-set-next-preserves-wellformed
    (implies (and (< (nfix next) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))
    :hints(("Goal" :in-theory (e/d (classes-wellformed)
                                   (node-set-next)))))

  (std::defret node-head-of-node-set-next
    (equal (node-head n (node-set-next m v classes))
           (node-head n classes))
    :hints(("Goal" :in-theory (enable node-head))))

  (std::defret node-next-of-node-set-next
    (equal (node-next n (node-set-next m v classes))
           (if (equal (nfix n) (nfix m))
               (nfix v)
             (node-next n classes)))
    :hints(("Goal" :in-theory (enable node-next)))))

(define node-set-head ((node natp) (head natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :returns (new-classes)
  (mbe :logic (update-class-headsi node (nfix head) classes)
       :exec (if (< head (ash 1 32))
                 (update-class-headsi node head classes)
               (non-exec (update-class-headsi node head classes))))
  ///
  (std::defret classes-size-of-node-set-head
    (<= (classes-size classes)
        (classes-size new-classes))
    :hints(("Goal" :in-theory (enable classes-size)))
    :rule-classes :linear)

  (std::defret classes-size-of-node-set-head-equal
    (implies (< (nfix node) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes)))
    :hints(("Goal" :in-theory (enable classes-size))))
  ;; (std::defret classes-sized-of-node-set-head
  ;;   (implies (classes-sized size classes)
  ;;            (classes-sized size new-classes))
  ;;   :hints(("Goal" :in-theory (enable classes-sized))))
  

  (std::defret node-set-head-preserves-wellformed-aux
    (implies (and (< (nfix head) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed-aux n classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux classes-size node-next node-head)
            :induct (classes-wellformed-aux n classes))))

  (std::defret node-set-head-preserves-wellformed
    (implies (and (< (nfix head) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))
    :hints(("Goal" :in-theory (e/d (classes-wellformed)
                                   (node-set-head)))))

  (std::defret node-next-of-node-set-head
    (equal (node-next n (node-set-head m v classes))
           (node-next n classes))
    :hints(("Goal" :in-theory (enable node-next))))

  (std::defret node-head-of-node-set-head
    (equal (node-head n (node-set-head m v classes))
           (if (equal (nfix n) (nfix m))
               (nfix v)
             (node-head n classes)))
    :hints(("Goal" :in-theory (enable node-head)))))

(define classes-init-aux ((n natp) classes)
  :guard (<= n (classes-size classes))
  :returns (new-classes)
  (if (zp n)
      classes
    (b* ((n-1 (1- n))
         (classes (node-set-head n-1 0 classes))
         (classes (node-set-next n-1 n classes)))
      (classes-init-aux n-1 classes)))
  ///
  ;; (std::defret classes-sized-of-classes-init-aux
  ;;   (implies (classes-sized size classes)
  ;;            (classes-sized size new-classes)))
  
  (std::defret classes-size-of-classes-init-aux
    (<= (classes-size classes)
        (classes-size new-classes))
    :rule-classes :linear)

  (std::defret classes-size-of-classes-init-aux-equal
    (implies (<= (nfix n) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  ;; (local (std::defret len-of-arrays-prserved-of-classes-init-aux-equal
  ;;          (implies (<= (nfix n) (classes-size classes))
  ;;                   (and (equal (len (nth *class-nextsi* new-classes))
  ;;                               (len (nth *class-nextsi* classes)))
  ;;                        (equal (len (nth *class-headsi* new-classes))
  ;;                               (len (nth *class-headsi* classes)))))
  ;;          :hints(("Goal" :in-theory (enable classes-size node-set-next node-set-head)))))

  (std::defret classes-init-aux-preserves-upper
    (implies (<= (nfix n) (nfix m))
             (and (equal (node-head m new-classes)
                         (node-head m classes))
                  (equal (node-next m new-classes)
                         (node-next m classes)))))

  (std::defret classes-wellformed-aux-of-classes-init-aux
    (implies (< n (classes-size classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )
            :induct t))))


(define classes-init ((size natp) classes)
  ;; Puts everything in one big equiv class.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ;; Set the last node separately because its next will be itself instead
       ;; of itself+1.
       (last (1- size))
       (classes (node-set-head last 0 classes))
       (classes (node-set-next last last classes))
       (classes (classes-init-aux last classes)))
    (node-set-head 0 last classes))
  ///

  (std::defret classes-size-of-classes-init
    (equal (classes-size new-classes) (nfix size)))

  (std::defret classes-wellformed-of-classes-init
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux size foo))
                           (:free (foo) (classes-wellformed-aux 0 foo))))))))




(define classes-init-filtered-aux ((n natp) (next acl2::maybe-natp) bitarr classes)
  :guard (and (<= n (classes-size classes))
              (or (not next)
                  (and (<= n next)
                       (< next (classes-size classes))))
              (<= (classes-size classes) (bits-length bitarr)))
  :guard-hints (("goal" :in-theory (enable acl2::maybe-natp)))
  :guard-debug t
  :returns (new-classes)
  (b* (((when (zp n)) classes)
       (n-1 (1- n))
       ((when (eql 0 (get-bit n-1 bitarr)))
        (b* ((classes (node-set-head n-1 n-1 classes))
             (classes (node-set-next n-1 n-1 classes)))
          (classes-init-filtered-aux (1- n) next bitarr classes)))
       (classes (node-set-head n-1 0 classes))
       (classes (node-set-next n-1 (if next (lnfix next) n-1) classes)))
    (classes-init-filtered-aux n-1 n-1 bitarr classes))
  ///
  (std::defret classes-size-of-classes-init-filtered-aux
    (<= (classes-size classes)
        (classes-size new-classes))
    :rule-classes :linear)

  (std::defret classes-size-of-classes-init-filtered-aux-equal
    (implies (<= (nfix n) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  ;; (local (std::defret len-of-arrays-prserved-of-classes-init-filtered-aux-equal
  ;;          (implies (<= (nfix n) (classes-size classes))
  ;;                   (and (equal (len (nth *class-nextsi* new-classes))
  ;;                               (len (nth *class-nextsi* classes)))
  ;;                        (equal (len (nth *class-headsi* new-classes))
  ;;                               (len (nth *class-headsi* classes)))))
  ;;          :hints(("Goal" :in-theory (enable classes-size node-set-next node-set-head)))))

  (std::defret classes-init-filtered-aux-preserves-upper
    (implies (<= (nfix n) (nfix m))
             (and (equal (node-head m new-classes)
                         (node-head m classes))
                  (equal (node-next m new-classes)
                         (node-next m classes)))))

  (std::defret classes-wellformed-aux-of-classes-init-filtered-aux
    (implies (and (<= (nfix n) (classes-size classes))
                  (implies next
                           (and (<= (nfix n) (nfix next))
                                (< (nfix next) (classes-size classes)))))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )
            :induct t))))

(define classes-init-outs-bitarr ((n natp) bitarr aignet)
  :guard (and (<= n (num-cos aignet))
              (< (max-fanin aignet) (bits-length bitarr)))
  :returns (new-bitarr)
  :prepwork ((local (defthm conum->id-is-lookup-conum
                      (implies (< (nfix n) (num-cos aignet))
                               (equal (conum->id n aignet)
                                      (node-count (lookup-conum n aignet))))
                      :hints(("Goal" :in-theory (enable conum->id lookup-conum))))))
  (b* (((when (zp n)) bitarr)
       (n-1 (1- n))
       (out-id (conum->id n-1 aignet))
       (fanin-id (if (int= (id->type out-id aignet) (out-type))
                      (lit-id (co-id->fanin out-id aignet))
                    out-id))
       (bitarr (set-bit fanin-id 1 bitarr)))
    (classes-init-outs-bitarr n-1 bitarr aignet))
  ///
  (defret bitarr-size-of-classes-init-outs-bitarr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  (defret bitarr-size-of-classes-init-outs-bitarr-equal
    (implies (and (< (max-fanin aignet) (len bitarr))
                  (<= (nfix n) (num-cos aignet)))
             (equal (len new-bitarr) (len bitarr)))))

(define classes-init-outs (classes aignet)
  ;; Puts everything in one big equiv class.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size)))))
             (local (in-theory (disable acl2::lower-bound-of-len-when-sublistp
                                        acl2::resize-list-when-atom))))
  :guard-hints (("goal" :do-not-induct t))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((size (+ 1 (max-fanin aignet)))
       (classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ((acl2::local-stobjs bitarr)
        (mv bitarr classes))
       (bitarr (resize-bits size bitarr))
       (bitarr (classes-init-outs-bitarr (num-cos aignet) bitarr aignet))
       ;; Always flag the constant node so that it will be in the class.
       (bitarr (set-bit 0 1 bitarr))
       (classes (classes-init-filtered-aux size nil bitarr classes)))
    (mv bitarr classes))
  ///

  (std::defret classes-size-of-classes-init-outs
    (equal (classes-size new-classes) (+ 1 (max-fanin aignet))))

  (std::defret classes-wellformed-of-classes-init-outs
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux 0 foo))))))))

(local (in-theory (disable unsigned-byte-p)))

(defmacro u32trunc (x)
  `(mbe :logic (acl2::loghead 32 ,x)
        :exec (the (unsigned-byte 32)
                   (logand #xffffffff ,x))))

(defmacro u32fix (x)
  `(mbe :logic (acl2::loghead 32 ,x)
        :exec (the (unsigned-byte 32) ,x)))

;; Bob Jenkins one-at-a-time hash
(define oathash1 ((byte :type (unsigned-byte 8))
                  (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (b* ((h (u32trunc (+ (u32fix h)
                       (mbe :logic (acl2::loghead 8 byte) :exec byte))))
       (h (u32trunc (+ h (ash h 10)))))
    (u32trunc (logxor h (ash h -6))))
  ///
  (std::defret unsigned-32-of-oathash1
    (unsigned-byte-p 32 new-h)))

(define oathash-u32 ((word :type (unsigned-byte 32))
                     (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (oathash1 (acl2::part-select word :low 24 :width 8)
            (oathash1 (acl2::part-select word :low 16 :width 8)
                      (oathash1 (acl2::part-select word :low 8 :width 8)
                                (oathash1 (acl2::part-select word :low 0 :width 8)
                                          h))))
  ///
  (std::defret unsigned-32-of-oathash-u32
    (unsigned-byte-p 32 new-h)))

(define oathash-s32 ((word :type (signed-byte 32))
                     (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (oathash1 (acl2::part-select word :low 24 :width 8)
            (oathash1 (acl2::part-select word :low 16 :width 8)
                      (oathash1 (acl2::part-select word :low 8 :width 8)
                                (oathash1 (acl2::part-select word :low 0 :width 8)
                                          h))))
  ///
  (std::defret unsigned-32-of-oathash-s32
    (unsigned-byte-p 32 new-h)))


(defthm s32ve-datap-is-s32-listp
  (equal (s32ve-datap x)
         (acl2::s32-listp x))
  :hints(("Goal" :in-theory (enable acl2::s32-listp))))

(defthm s32-listp-nth-of-s32vl-data
  (implies (s32vl-arr2-data-wfp x width)
           (acl2::s32-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))

(local (in-theory (enable ACL2::NTH-IN-S32-LISTP-S32P)))
(local (in-theory (disable signed-byte-p)))

(local (fty::deffixcong bit-equiv equal (bit-extend bit) bit
         :hints(("Goal" :in-theory (enable bit-extend)))))

(define s32-apply-parity ((x (signed-byte-p 32 x):type (signed-byte 32))
                          (parity bitp :type bit))
  :split-types t
  :returns (new-x integerp :rule-classes :type-prescription)
  (logxor (mbe :logic (acl2::logext 32 x) :exec x)
          (bit-extend parity))
  ///
  (defret signed-32-of-u32-apply-parity
    (signed-byte-p 32 new-x)))

(define oathash-s32v-aux ((row natp :type (integer 0 *))
                          (col natp :type (integer 0 *))
                          (h (unsigned-byte-p 32 h) :type (unsigned-byte 32))
                          (parity bitp :type bit)
                          s32v)
  :split-types t
  :guard (and (< row (s32v-nrows s32v))
              (<= col (s32v-ncols s32v)))
  :measure (nfix (- (s32v-ncols s32v) (nfix col)))
  :returns (new-h)
  (if (mbe :logic (zp (- (s32v-ncols s32v) (nfix col)))
           :exec (eql col (s32v-ncols s32v)))
      (u32fix h)
    (oathash-s32v-aux row (+ 1 (lnfix col))
                      (oathash-s32 (s32-apply-parity (s32v-get2 row col s32v) parity)
                                   h)
                      parity
                      s32v))
  ///
  (std::defret unsigned-32-of-oathash-s32v-aux
    (unsigned-byte-p 32 new-h)))

(define oathash-s32v ((row natp) (parity bitp) s32v)
  :guard (< row (s32v-nrows s32v))
  :returns (h)
  (b* ((h (oathash-s32v-aux row 0 0 parity s32v))
       (h (u32trunc (+ h (ash h 3))))
       (h (u32trunc (logxor h (ash h -11))))
       (h (u32trunc (+ h (ash h 15)))))
    h)
  ///
  (std::defret unsigned-32-of-oathash-s32v
    (unsigned-byte-p 32 h)))
       
  
(defstobj classhash      
  ;; Maps hashes of s32v values to a list* of nodes.
  (classhash-table :type (hash-table eql))
  :inline t)

(define s32v-compare-aux ((row1 natp)
                          (row2 natp)
                          (parity1 bitp)
                          (parity2 bitp)
                          (col natp)
                          s32v)
  :guard (and (< row1 (s32v-nrows s32v))
              (< row2 (s32v-nrows s32v))
              (<= col (s32v-ncols s32v)))
  :measure (nfix (- (s32v-ncols s32v) (nfix col)))
  :returns (equalp)
  :prepwork ((local (defthm eqlablep-when-natp
                      (implies (natp x)
                               (eqlablep x)))))
  (if (mbe :logic (zp (- (s32v-ncols s32v) (nfix col)))
           :exec (eql col (s32v-ncols s32v)))
      t
    (and (eql (s32-apply-parity (s32v-get2 row1 col s32v) parity1)
              (s32-apply-parity (s32v-get2 row2 col s32v) parity2))
         (s32v-compare-aux row1 row2 parity1 parity2 (1+ (lnfix col)) s32v))))

(define s32v-compare ((row1 natp)
                      (row2 natp)
                      (parity1 bitp)
                      (parity2 bitp)
                      s32v)
  :guard (and (< row1 (s32v-nrows s32v))
              (< row2 (s32v-nrows s32v)))
  (s32v-compare-aux row1 row2 parity1 parity2 0 s32v))

(define classes-hash-find-aux ((node natp)
                               (lookup)
                               (s32v)
                               aignet)
  :guard (and (< node (s32v-nrows s32v))
              (< node (num-nodes aignet)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (match (or (not match) (natp match)) :rule-classes :type-prescription)
  (b* (((unless lookup) nil)
       ((mv try end) (if (consp lookup)
                         (mv (car lookup) nil)
                       (mv lookup t)))
       ((when (and (natp try)
                   (< try (lnfix node))
                   (s32v-compare node try (id->phase node aignet) (id->phase try aignet) s32v)))
        try)
       ((when end) nil))
    (classes-hash-find-aux node (cdr lookup) s32v aignet))
  ///
  (std::defret classes-hash-find-aux-bound
    (implies match
             (< match (nfix node)))))
            
                               
  
(define classes-hash-find ((node natp)
                           (hash :type (unsigned-byte 32))
                           (s32v)
                           (classhash)
                           (aignet))
  :guard (and (< node (s32v-nrows s32v))
              (< node (num-nodes aignet)))
  :returns (match (or (not match) (natp match)) :rule-classes :type-prescription)
  (b* ((lookup (classhash-table-get hash classhash)))
    (classes-hash-find-aux node lookup s32v aignet))
  ///
  (std::defret classes-hash-find-bound
    (implies match
             (< match (nfix node)))
    :rule-classes :linear))

(define classes-hash-add ((node natp)
                          (hash :type (unsigned-byte 32))
                          (classhash))
  (b* ((lookup (classhash-table-get hash classhash)))
    (classhash-table-put hash (if lookup (cons (lnfix node) lookup) (lnfix node)) classhash)))
       

(define u32-list-p (x)
  :enabled t
  (or (null x) (and (consp x) (unsigned-byte-p 32 (first x)) (u32-list-p (rest x)))))

(define classes-hash-rem-lst ((rem-hash-lst u32-list-p)
                              (classhash))
  (if (endp rem-hash-lst) classhash
    (b* ((classhash (classhash-table-rem (first rem-hash-lst) classhash)))
      (classes-hash-rem-lst (rest rem-hash-lst) classhash))))

(define classes-refine-class-aux ((prev natp)
                                  (node natp)
                                  (nrefines natp)
                                  (rem-hash-lst u32-list-p)
                                  (s32v)
                                  (classhash)
                                  (classes)
                                  (aignet))
  ;; Node is always in the class of prev.  When we start prev is the head node and node is its next.
  ;; When its next turns out to be part of the same class, we then iterate on next with node as prev.  The
  ;; first node not in the same class as the head becomes head of its own class.
  ;; Its head is updated to the tail of the class as more nodes get added.
  ;;
  ;; Added rem-hash-lst parameter to avoid non-tail call which removed
  ;; hashtable entries after recursive call..
  :guard (and (<= prev node)
              (< node (classes-size classes))
              (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-nodes aignet))
              (classes-wellformed classes))
  :Guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (classes-size classes) (nfix node)))
  :returns (mv new-classhash
               new-classes
               (nrefines-out natp :rule-classes :type-prescription))
  (b* ((node (lnfix node)) (prev (lnfix prev)) (nrefines (lnfix nrefines))
       ((unless (mbt (and (< node (classes-size classes))
                          (< prev (classes-size classes))
                          (classes-wellformed classes))))
        (b* ((classhash (classes-hash-rem-lst rem-hash-lst classhash)))
          (mv classhash classes nrefines)))
       (head (node-head node classes))
       (same (s32v-compare head node
                           (id->phase head aignet)
                           (id->phase node aignet)
                           s32v))
       (next (node-next node classes))
       ((when same)
        ;; (cw "same~%")
        ;; stays in this class; ensure next of prev points to this node
        (b* ((classes (node-set-next prev node classes)))
          (if (<= next node)
              ;; was the last node in the class, so set head of head to this
              (b* ((classes (node-set-head head node classes))
                   (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
                (mv classhash classes nrefines))
            (classes-refine-class-aux node next nrefines rem-hash-lst s32v classhash classes aignet))))
       (nrefines  (+ 1 nrefines))
       (hash (oathash-s32v node (id->phase node aignet) s32v))
       (match (classes-hash-find node hash s32v classhash aignet))
       ((unless match)
        ;; (cw "head~%")
        ;; node breaks off into its own class, iterate on prev/next
        (b* ((classes (node-set-head node node classes))
             (classes (node-set-next node node classes))
             ((when (<= next node))
              (b* ((classes (node-set-head head prev classes))
                   (classes (node-set-next prev head classes))
                   (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
                (mv classhash classes nrefines)))
             (classhash (classes-hash-add node hash classhash))
             (rem-hash-lst (cons hash rem-hash-lst)))
          (classes-refine-class-aux prev next nrefines rem-hash-lst s32v classhash classes aignet)))
       ;; (- (cw "match ~x0~%" match))
       ;; match is a head node, so its head is the last in its class -- set it to point to node
       (classes (node-set-next (node-head match classes) node classes))
       (classes (node-set-head match node classes))
       (classes (node-set-head node match classes))
       (classes (node-set-next node match classes))
       ((when (<= next node))
        (b* ((classes (node-set-head head prev classes))
             (classes (node-set-next prev head classes))
             (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
          (mv classhash classes nrefines))))
    (classes-refine-class-aux prev next nrefines rem-hash-lst s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine-class-aux
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine-class-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))

(define classhash-table-clear-prof (classhash)
  :enabled t
  (classhash-table-clear classhash))

;; (define classes-refine-class ((node natp)
;;                               (s32v)
;;                               (classhash)
;;                               (classes)
;;                               (aignet))
;;   ;; :inline t
;;   :guard (and (< node (classes-size classes))
;;               (equal (classes-size classes) (s32v-nrows s32v))
;;               (<= (classes-size classes) (num-nodes aignet))
;;               (classes-wellformed classes))
;;   :returns (mv new-classhash
;;                new-classes
;;                (nrefines-out natp :rule-classes :type-prescription))
;;   (b* ((node (lnfix node))
       ;; ((when (or (>= node (node-head node classes))
       ;;            (< (node-next node classes) node)))
;;        ;;  ;; Either node is not the head or it is in a singleton class, so no refinement.
;;        ;;  (mv classhash classes 0))
;;        ;; (classhash (classhash-table-clear-prof classhash))
;;        )
;;     (classes-refine-class-aux node (node-next node classes) 0
;;                               s32v classhash classes aignet))
;;   ///
  
;;   (std::defret classes-size-of-classes-refine-class
;;     (equal (classes-size new-classes) (classes-size classes)))

;;   (std::defret classes-wellformed-of-classes-refine-class
;;     (implies (classes-wellformed classes)
;;              (classes-wellformed new-classes))))


(define show-class-nexts ((n natp) classes)
  :measure (nfix (- (classes-size classes) (nfix n)))
  :guard (<= n (classes-size classes))
  (if (zp (- (classes-size classes) (nfix n)))
      nil
    (cons (node-next n classes)
          (show-class-nexts (1+ (lnfix n)) classes))))

(define show-class-heads ((n natp) classes)
  :measure (nfix (- (classes-size classes) (nfix n)))
  :guard (<= n (classes-size classes))
  (if (zp (- (classes-size classes) (nfix n)))
      nil
    (cons (node-head n classes)
          (show-class-heads (1+ (lnfix n)) classes))))

(Define show-classes (classes)
  (list (cons :nexts (show-class-nexts 0 classes))
        (cons :heads (show-class-heads 0 classes))))


(define classes-refine-update-stats ((node natp)
                                     (nrefines-class natp)
                                     (nclass-lits-refined natp)
                                     (nconst-lits-refined natp)
                                     (nclasses-refined natp))
  :inline t
  :returns (mv (nclass-lits-refined-out natp :rule-classes :type-prescription)
               (nconst-lits-refined-out natp :rule-classes :type-prescription)
               (nclasses-refined-out natp :rule-classes :type-prescription))
  (b* ((nclasses-refined (+ (if (eql 0 (lnfix nrefines-class)) 0 1) (lnfix nclasses-refined))))
    (if (mbe :logic (zp node) :exec (eql node 0))
        (mv (lnfix nclass-lits-refined)
            (+ (lnfix nrefines-class) (lnfix nconst-lits-refined))
            nclasses-refined)
      (mv (+ (lnfix nrefines-class) (lnfix nclass-lits-refined))
            (lnfix nconst-lits-refined)
            nclasses-refined))))
                                     


(define classes-refine-aux ((node natp :type (integer 0 *))
                            (nclass-lits-refined natp :type (integer 0 *))
                            (nconst-lits-refined natp :type (integer 0 *))
                            (nclasses-refined natp :type (integer 0 *))
                            (s32v)
                            (classhash)
                            (classes)
                            (aignet))
  ;; This loop needs to be really highly optimized, especially for singleton nodes!
  :guard (and (<= node (classes-size classes))
              (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-nodes aignet))
              (classes-wellformed classes))
  :split-types t
  :returns (mv new-classhash
               new-classes
               (nclass-lits-refined-out natp :rule-classes :type-prescription)
               (nconst-lits-refined-out natp :rule-classes :type-prescription)
               (nclasses-refined-out natp :rule-classes :type-prescription))
  (b* (((when (mbe :logic (zp node)
                   :exec (int= node 0)))
        (mv classhash classes (lnfix nclass-lits-refined) (lnfix nconst-lits-refined) (lnfix nclasses-refined)))
       (node (the (integer 0 *)
                  (+ -1 (the (integer 0 *) node))))
       ((when ;; if head is less, node is in a class but is not not the head node; if equal, it's a singleton
            (or (>= (the (integer 0 *) node)
                    (the (integer 0 *) (node-head node classes)))
                (< (the (integer 0 *) (node-next node classes))
                   (the (integer 0 *) node))
                ))
        (classes-refine-aux node nclass-lits-refined nconst-lits-refined nclasses-refined
                            s32v classhash classes aignet))
       ((mv classhash classes nrefines-class) (classes-refine-class-aux node (node-next node classes)
                                                                        0 nil s32v classhash classes aignet))
       ((mv nclass-lits-refined nconst-lits-refined nclasses-refined)
        (classes-refine-update-stats node nrefines-class nclass-lits-refined nconst-lits-refined nclasses-refined)))
    (classes-refine-aux node nclass-lits-refined nconst-lits-refined nclasses-refined
                        s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine-aux
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))

(define classes-refine ((s32v)
                        (classes)
                        (aignet))
  :guard (and (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-nodes aignet))
              (classes-wellformed classes))
  :returns (mv new-classes
               (nclass-lits-refined natp :rule-classes :type-prescription)
               (nconst-lits-refined natp :rule-classes :type-prescription)
               (nclasses-refined natp :rule-classes :type-prescription))
  ;; might be memory hungry to keep recreating classhash?
  (b* (((acl2::local-stobjs classhash)
        (mv classhash classes nclass-lits-refined nconst-lits-refined nclasses-refined)))
    (classes-refine-aux (classes-size classes) 0 0 0 s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))


  
    
(define classes-counts-aux ((n natp)
                            (max natp)
                            (nclasses natp)
                            (nconst-lits natp)
                            (nclass-lits natp)
                            (classes))
  :guard (and (eql max (classes-size classes))
              (<= (nfix n) (classes-size classes)))
  :returns (mv (nclasses-out natp :rule-classes :type-prescription)
               (nconst-lits-out natp :rule-classes :type-prescription)
               (nclass-lits-out natp :rule-classes :type-prescription))
  :measure (nfix (- (classes-size classes) (nfix n)))
  ;; The three stats returned are disjoint subsets of the nodes, so the number of nodes with no equivalences is
  ;; (- (num-nodes) (+ nconst-lits nclasses nclass-lits)) (where the 1 is for the constant-0 node).
  (b* ((nclasses (lnfix nclasses))
       (nconst-lits (lnfix nconst-lits))
       (nclass-lits (lnfix nclass-lits))
       ((when (mbe :logic (zp (- (classes-size classes) (nfix n)))
                   :exec (eql n max)))
        (mv nclasses nconst-lits nclass-lits))
       (n (lnfix n))
       ((mv nclasses nconst-lits nclass-lits)
        (b* (((when (eql 0 (node-head n classes)))
              ;; node is equivalent to 0
              (if (eql n 0)
                  (mv nclasses nconst-lits nclass-lits)
                (mv nclasses (+ 1 nconst-lits) nclass-lits)))
             ((when (< (node-head n classes) n))
              ;; node is in some other equivalence class
              (mv nclasses nconst-lits (+ 1 nclass-lits)))
             ;; node is its own head -- check whether it has a next, otherwise it's a singleton class
             ((when (<= (node-next n classes) n))
              (mv nclasses nconst-lits nclass-lits)))
          (mv (+ 1 nclasses) nconst-lits nclass-lits))))
    (classes-counts-aux (1+ n) max nclasses nconst-lits nclass-lits classes)))

(define classes-counts (classes &key ((start-node natp) '0))
  :guard (<= start-node (classes-size classes))
  :returns (mv (nclasses natp :rule-classes :type-prescription)
               (nconst-lits natp :rule-classes :type-prescription)
               (nclass-lits natp :rule-classes :type-prescription))
  (classes-counts-aux start-node (classes-size classes) 0 0 0 classes))

