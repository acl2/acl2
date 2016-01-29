; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "u32-listp")
(include-book "std/basic/defs" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "arith-equivs")
(include-book "absstobjs")
(include-book "tools/mv-nth" :dir :system)
(include-book "lists")
(include-book "misc/definline" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(in-theory (enable* arith-equiv-forwarding))

(local (in-theory (disable nth update-nth)))

;; this is a dumb "memory manager" which can allocate new blocks at will, but
;; only frees any blocks if it frees all blocks.

(defstobj smme
  (smme-nblocks :type (integer 0 *) :initially 0)
  ;; one larger than smme-blocksizes
  (smme-blockstarts :type (array (integer 0 *) (1))
                   :initially 0
                   :resizable t)
  (smme-blocksizes :type (array (integer 0 *) (0))
                  :initially 0
                  :resizable t)
  ;; 32-bit unsigneds for now, why not
  (smme-mem :type (array (unsigned-byte 32) (0))
           :initially 0
           :resizable t)
  :inline t)

(defthm smme-blockstarts-p-nat-listp
  (equal (smme-blockstartsp x)
         (nat-listp x)))

(defthm smme-blocksizes-p-nat-listp
  (equal (smme-blocksizesp x)
         (nat-listp x)))

(local (defthm nth-in-nat-listp
         (implies (and (nat-listp x)
                       (< (nfix n) (len x)))
                  (and (integerp (nth n x))
                       (<= 0 (nth n x))))
         :hints(("Goal" :in-theory (enable nth)))
         :rule-classes (:rewrite
                        (:rewrite :corollary
                         (implies (and (nat-listp x)
                                       (< (nfix n) (len x)))
                                  (natp (nth n x))))
                        ;; :type-prescription
                        (:linear :corollary
                         (implies (and (nat-listp x)
                                       (< (nfix n) (len x)))
                                  (<= 0 (nth n x)))))))

(local (defthm rationalp-+-of-integers
         (implies (and (integerp x) (integerp y))
                  (rationalp (+ x y)))))

(defun smme-sizes-okp (smme)
  (declare (xargs :stobjs smme))
  (and (< (lnfix (smme-nblocks smme))
          (smme-blockstarts-length smme))
       (<= (lnfix (smme-nblocks smme))
           (smme-blocksizes-length smme))
       (<= (lnfix (smme-blockstartsi (smme-nblocks smme) smme))
           (smme-mem-length smme))))


(definline smme-block-start (n smme)
  (declare (xargs :guard (and (natp n)
                              (<= n (smme-nblocks smme))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (lnfix (smme-blockstartsi n smme)))

(defcong nat-equiv equal (smme-block-start n smme) 1)

(definline smme-block-size (n smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (lnfix (smme-blocksizesi n smme)))

(defcong nat-equiv equal (smme-block-size n smme) 1)


(defun smme-blocks-wfp (n smme)
  (declare (xargs :guard (and (natp n)
                              (<= n (lnfix (smme-nblocks smme)))
                              (smme-sizes-okp smme))
                  :stobjs smme))
  (or (zp n)
      (and (int= (smme-block-start n smme)
                 (+ (smme-block-start (1- n) smme)
                    (smme-block-size (1- n) smme)))
           (smme-blocks-wfp (1- n) smme))))

(defcong nat-equiv equal (smme-blocks-wfp n smme) 1)



(defun smme-wfp (smme)
  (declare (xargs :stobjs smme))
  (and (smme-sizes-okp smme)
       (int= 0 (smme-block-start 0 smme))
       (smme-blocks-wfp (smme-nblocks smme) smme)))


(definline smme-addr (n i smme)
  (declare (xargs :stobjs smme
                  :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme)))))
  (+ (lnfix i)
     (smme-block-start n smme)))

(defcong nat-equiv equal (smme-addr n i smme) 1)
(defcong nat-equiv equal (smme-addr n i smme) 2)

(defthm smme-blocks-wfp-implies-block-ref-in-bounds
  (implies (and (smme-blocks-wfp m smme)
                (< (nfix n) (nfix m))
                (< (nfix i) (smme-block-size n smme)))
           (< (smme-addr n i smme)
              (nfix (nth m (nth *smme-blockstartsi* smme)))))
  :rule-classes :linear)

(defthm smme-wfp-implies-block-ref-in-bounds
  (implies (and (smme-wfp smme)
                (< (nfix n) (nfix (smme-nblocks smme)))
                (< (nfix i) (smme-block-size n smme)))
           (< (smme-addr n i smme)
              (nfix (nth (nth *smme-nblocks* smme)
                         (nth *smme-blockstartsi* smme)))))
  :hints(("Goal" :in-theory (disable smme-addr smme-block-start)))
  :rule-classes (:rewrite (:linear :trigger-terms ((smme-addr n i smme)))))


(defthm smme-blocks-wfp-implies-block-refs-differ
  (implies (and (smme-blocks-wfp m smme)
                (< (nfix n) (nfix m))
                (< (nfix i) (smme-block-size n smme)))
           (< (smme-addr n i smme)
              (smme-addr m j smme)))
  :rule-classes (:rewrite :linear))

(defthm smme-blocks-wfp-for-smaller-n
  (implies (and (smme-blocks-wfp m smme)
                (<= (nfix n) (nfix m)))
           (smme-blocks-wfp n smme)))


(defthm smme-wfp-implies-block-refs-differ-1
  (implies (and (smme-wfp smme)
                (< (nfix n1) (nfix n2))
                (< (nfix n2) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme)))
           (< (smme-addr n1 i1 smme)
              (smme-addr n2 i2 smme)))
  :hints(("Goal" :in-theory (disable smme-addr)))
  :rule-classes (:rewrite :linear))

(defthm smme-wfp-implies-block-refs-differ
  (implies (and (smme-wfp smme)
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix n2) (nfix (smme-nblocks smme)))
                (not (equal (nfix n1) (nfix n2)))
                (< (nfix i1) (smme-block-size n1 smme))
                (< (nfix i2) (smme-block-size n2 smme)))
           (not (equal (smme-addr n1 i1 smme)
                       (smme-addr n2 i2 smme))))
  :hints (("goal" :use ((:instance smme-wfp-implies-block-refs-differ-1)
                        (:instance smme-wfp-implies-block-refs-differ-1
                         (n1 n2) (n2 n1) (i1 i2) (i2 i1))))))

(defthm smme-addrs-with-different-i
  (implies (not (equal (nfix i1) (nfix i2)))
           (not (equal (smme-addr n i1 smme)
                       (smme-addr n i2 smme)))))

(defthm smme-wfp-implies-block-refs-differ-in-n-or-i
  (implies (and (smme-wfp smme)
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix n2) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme))
                (< (nfix i2) (smme-block-size n2 smme))
                (or (not (equal (nfix n1) (nfix n2)))
                    (not (equal (nfix i1) (nfix i2)))))
           (not (equal (smme-addr n1 i1 smme)
                       (smme-addr n2 i2 smme))))
  :hints (("Goal" :cases ((equal (nfix n1) (nfix n2)))
           :in-theory (disable smme-addr))))

(in-theory (disable smme-addr))


(definline smme-read (n i smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme)))
                  :stobjs smme))
  (smme-memi (smme-addr n i smme) smme))

(definline smme-write (n i v smme)
  (declare (xargs :guard (and (natp n)
                              (< n (smme-nblocks smme))
                              (smme-wfp smme)
                              (natp i)
                              (< i (smme-block-size n smme))
                              (unsigned-byte-p 32 v))
                  :stobjs smme))
  (update-smme-memi (smme-addr n i smme) v smme))

(defthm smme-addr-of-update-mem
  (equal (smme-addr n i (update-nth *smme-memi* v smme))
         (smme-addr n i smme))
  :hints(("Goal" :in-theory (enable smme-addr))))


(defthmd smme-read-of-smme-write-split
  (implies (and (smme-wfp smme)
                (< (nfix nr) (nfix (smme-nblocks smme)))
                (< (nfix ir) (smme-block-size nr smme))
                (< (nfix nw) (nfix (smme-nblocks smme)))
                (< (nfix iw) (smme-block-size nw smme)))
           (equal (smme-read nr ir (smme-write nw iw v smme))
                  (if (and (equal (nfix nr) (nfix nw))
                           (equal (nfix ir) (nfix iw)))
                      v
                    (smme-read nr ir smme))))
  :hints(("Goal" :in-theory (disable smme-wfp)
          :cases ((equal (nfix nr) (nfix nw))))))

(defthm smme-write-of-smme-write-same
  (implies (and (and (equal (nfix n1) (nfix n2))
                     (equal (nfix i1) (nfix i2)))
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme)))
           (equal (smme-write n1 i1 v1 (smme-write n2 i2 v2 smme))
                  (smme-write n1 i1 v1 smme))))


(defthm smme-write-of-smme-write-diff
  (implies (and (smme-wfp smme)
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme))
                (< (nfix n2) (nfix (smme-nblocks smme)))
                (< (nfix i2) (smme-block-size n2 smme))
                (or (not (equal (nfix n1) (nfix n2)))
                    (not (equal (nfix i1) (nfix i2)))))
           (equal (smme-write n1 i1 v1 (smme-write n2 i2 v2 smme))
                  (smme-write n2 i2 v2 (smme-write n1 i1 v1 smme))))
  :hints (("goal" :cases ((< (smme-addr n1 i1 smme)
                             (smme-addr n2 i2 smme))
                          (< (smme-addr n2 i2 smme)
                             (smme-addr n1 i1 smme)))
           :in-theory (disable smme-wfp))
          '(:cases ((equal (nfix n1) (nfix n2))))))

(defthm smme-read-of-smme-write-same
  (implies (and (and (equal (nfix n1) (nfix n2))
                     (equal (nfix i1) (nfix i2)))
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme)))
           (equal (smme-read n1 i1 (smme-write n2 i2 v2 smme))
                  v2)))


(defthm smme-read-of-smme-write-diff
  (implies (and (smme-wfp smme)
                (< (nfix n1) (nfix (smme-nblocks smme)))
                (< (nfix i1) (smme-block-size n1 smme))
                (< (nfix n2) (nfix (smme-nblocks smme)))
                (< (nfix i2) (smme-block-size n2 smme))
                (or (not (equal (nfix n1) (nfix n2)))
                    (not (equal (nfix i1) (nfix i2)))))
           (equal (smme-read n1 i1 (smme-write n2 i2 v2 smme))
                  (smme-read n1 i1 smme)))
  :hints (("goal" :cases ((equal (nfix n1) (nfix n2)))
           :in-theory (disable smme-wfp))))


(defthm smme-blocks-wfp-of-update-memi
  (equal (smme-blocks-wfp n (update-nth *smme-memi* v smme))
         (smme-blocks-wfp n smme)))

(defthm smme-wfp-of-smme-write
  (implies (smme-wfp smme)
           (smme-wfp (smme-write n i v smme))))


(defthm smme-block-size-of-smme-write
  (equal (smme-block-size n1 (smme-write n i v smme))
         (smme-block-size n1 smme)))

(defthm smme-nblocks-of-smme-write
  (equal (smme-nblocks (smme-write n i v smme))
         (smme-nblocks smme)))


(local (defthm max-linear-1
         (<= a (max a b))
         :rule-classes :linear))

(local (defthm max-linear-2
         (<= b (max a b))
         :rule-classes :linear))


(local (defthm *-2-nfix-linear
         (<= (nfix n) (* 2 (nfix n)))
         :rule-classes :linear))

(defthm nat-listp-resize-list
  (implies (and (nat-listp lst)
                (natp default))
           (nat-listp (resize-list lst n default))))

(defthm smme-memp-is-u32-listp
  (equal (smme-memp x)
         (u32-listp x)))

(defthm u32-listp-resize-list
  (implies (and (u32-listp lst)
                (unsigned-byte-p 32 default))
           (u32-listp (resize-list lst n default))))

(definline smme-maybe-resize-sizes (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-blocksizes-length smme))
      smme
    (resize-smme-blocksizes (max 16 (* 2 (lnfix n))) smme)))


(defthm blocksize-of-smme-maybe-resize-sizes
  (equal (nfix (nth m (nth *smme-blocksizesi* (smme-maybe-resize-sizes n smme))))
         (nfix (nth m (nth *smme-blocksizesi* smme))))
  :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

(defthm len-sizes-of-smme-maybe-resize-sizes
  (< (nfix n)
     (len (nth *smme-blocksizesi* (smme-maybe-resize-sizes n smme))))
  :rule-classes :linear)

(defthm nth-of-smme-maybe-resize-sizes
  (implies (not (equal i *smme-blocksizesi*))
           (equal (nth i (smme-maybe-resize-sizes n smme))
                  (nth i smme))))

(defthm smme-blocks-wfp-of-smme-maybe-resize-sizes
  (equal (smme-blocks-wfp m (smme-maybe-resize-sizes n smme))
         (smme-blocks-wfp m smme))
  :hints (("goal" :induct (smme-blocks-wfp m smme)
           :in-theory (disable smme-maybe-resize-sizes))))

(defthm true-listp-smme-maybe-resize-sizes
  (implies (true-listp smme)
           (true-listp (smme-maybe-resize-sizes n smme)))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-sizes))))

(defthm len-of-smme-maybe-resize-sizes
  (implies (equal (len smme) 4)
           (equal (len (smme-maybe-resize-sizes sz smme)) 4))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-sizes))))

(defthm len-sizes-of-smme-maybe-resize-sizes-linear1
  (< (nfix n)
     (len (nth *smme-blocksizesi*
               (smme-maybe-resize-sizes n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-sizes)))
  :rule-classes :linear)

(defthm len-sizes-of-smme-maybe-resize-sizes-linear2
  (<= (len (nth *smme-blocksizesi* smme))
      (len (nth *smme-blocksizesi*
                (smme-maybe-resize-sizes n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-sizes)))
  :rule-classes :linear)

(defthm nat-listp-sizes-of-smme-maybe-resize-sizes
  (implies (nat-listp (nth *smme-blocksizesi* smme))
           (nat-listp (nth *smme-blocksizesi*
                           (smme-maybe-resize-sizes n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-sizes))))

(definline smme-maybe-resize-starts (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-blockstarts-length smme))
      smme
    (resize-smme-blockstarts (max 16 (* 2 (lnfix n))) smme)))

(defthm blockstart-of-smme-maybe-resize-starts
  (equal (nfix (nth m (nth *smme-blockstartsi* (smme-maybe-resize-starts n smme))))
         (nfix (nth m (nth *smme-blockstartsi* smme))))
  :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

(defthm len-starts-of-smme-maybe-resize-starts
  (< (nfix n)
     (len (nth *smme-blockstartsi* (smme-maybe-resize-starts n smme))))
  :rule-classes :linear)

(defthm nth-of-smme-maybe-resize-starts
  (implies (not (equal i *smme-blockstartsi*))
           (equal (nth i (smme-maybe-resize-starts n smme))
                  (nth i smme))))

(defthm smme-blocks-wfp-of-smme-maybe-resize-starts
  (equal (smme-blocks-wfp m (smme-maybe-resize-starts n smme))
         (smme-blocks-wfp m smme))
  :hints (("goal" :induct (smme-blocks-wfp m smme)
           :in-theory (disable smme-maybe-resize-starts))))

(defthm true-listp-smme-maybe-resize-starts
  (implies (true-listp smme)
           (true-listp (smme-maybe-resize-starts n smme)))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-starts))))

(defthm len-of-smme-maybe-resize-starts
  (implies (equal (len smme) 4)
           (equal (len (smme-maybe-resize-starts sz smme)) 4))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-starts))))

(defthm len-starts-of-smme-maybe-resize-starts-linear1
  (< (nfix n)
     (len (nth *smme-blockstartsi*
               (smme-maybe-resize-starts n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-starts)))
  :rule-classes :linear)

(defthm len-starts-of-smme-maybe-resize-starts-linear2
  (<= (len (nth *smme-blockstartsi* smme))
      (len (nth *smme-blockstartsi*
                (smme-maybe-resize-starts n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-starts)))
  :rule-classes :linear)

(defthm nat-listp-starts-of-smme-maybe-resize-starts
  (implies (nat-listp (nth *smme-blockstartsi* smme))
           (nat-listp (nth *smme-blockstartsi*
                           (smme-maybe-resize-starts n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-starts))))


(definline smme-maybe-resize-mem (n smme)
  (declare (xargs :stobjs smme
                  :guard (natp n)))
  (if (< (lnfix n) (smme-mem-length smme))
      smme
    (resize-smme-mem (max 16 (* 2 (lnfix n))) smme)))


(defthm memi-of-smme-maybe-resize-mem
  (implies (< (nfix m) (len (nth *smme-memi* smme)))
           (equal (nth m (nth *smme-memi* (smme-maybe-resize-mem n smme)))
                  (nth m (nth *smme-memi* smme)))))

(defthm len-mem-of-smme-maybe-resize-mem
  (< (nfix n)
     (len (nth *smme-memi* (smme-maybe-resize-mem n smme))))
  :rule-classes :linear)

(defthm nth-of-smme-maybe-resize-mem
  (implies (not (equal i *smme-memi*))
           (equal (nth i (smme-maybe-resize-mem n smme))
                  (nth i smme))))

(defthm smme-blocks-wfp-of-smme-maybe-resize-mem
  (equal (smme-blocks-wfp m (smme-maybe-resize-mem n smme))
         (smme-blocks-wfp m smme))
  :hints (("goal" :induct (smme-blocks-wfp m smme)
           :in-theory (disable smme-maybe-resize-mem))))

(defthm true-listp-smme-maybe-resize-mem
  (implies (true-listp smme)
           (true-listp (smme-maybe-resize-mem n smme)))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-mem))))

(defthm len-of-smme-maybe-resize-mem
  (implies (equal (len smme) 4)
           (equal (len (smme-maybe-resize-mem sz smme)) 4))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-mem))))

(defthm len-mem-of-smme-maybe-resize-mem-linear1
  (< (nfix n)
     (len (nth *smme-memi*
               (smme-maybe-resize-mem n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-mem)))
  :rule-classes :linear)

(defthm len-mem-of-smme-maybe-resize-mem-linear2
  (<= (len (nth *smme-memi* smme))
      (len (nth *smme-memi*
                (smme-maybe-resize-mem n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-mem)))
  :rule-classes :linear)

(defthm u32-listp-mem-of-smme-maybe-resize-mem
  (implies (u32-listp (nth *smme-memi* smme))
           (u32-listp (nth *smme-memi*
                          (smme-maybe-resize-mem n smme))))
  :hints(("Goal" :in-theory (enable smme-maybe-resize-mem))))



(in-theory (disable smme-maybe-resize-sizes
                    smme-maybe-resize-starts
                    smme-maybe-resize-mem))

(defun smme-mem-clear (n max val smme)
  (declare (xargs :guard (and (natp n)
                              (natp max)
                              (<= n max)
                              (<= max (smme-mem-length smme))
                              (unsigned-byte-p 32 val))
                  :stobjs smme
                  :measure (nfix (- (nfix max) (nfix n)))))
  (if (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (int= max n))
      smme
    (let ((smme (update-smme-memi n val smme)))
      (smme-mem-clear (+ 1 (lnfix n)) max val smme))))

(defthm nth-of-smme-mem-clear
  (implies (not (equal m *smme-memi*))
           (equal (nth m (smme-mem-clear n max val smme))
                  (nth m smme))))

(defthm memi-of-smme-mem-clear
  (equal (nth m (nth *smme-memi* (smme-mem-clear n max val smme)))
         (if (and (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix max)))
             val
           (nth m (nth *smme-memi* smme)))))

(defthm smme-blocks-wfp-of-smme-mem-clear
  (equal (smme-blocks-wfp m (smme-mem-clear n max val smme))
         (smme-blocks-wfp m smme)))

(defthm mem-length-of-smme-mem-clear
  (implies (<= (nfix max) (len (nth *smme-memi* smme)))
           (equal (len (nth *smme-memi* (smme-mem-clear n max val smme)))
                  (len (nth *smme-memi* smme)))))

(defthm true-listp-smme-mem-clear
  (implies (true-listp smme)
           (true-listp (smme-mem-clear n max val smme))))

(defthm len-of-smme-mem-clear
  (implies (equal (len smme) 4)
           (equal (len (smme-mem-clear n max val smme)) 4)))

(local (defthm u32-listp-update-nth
         (implies (and (unsigned-byte-p 32 v)
                       (< (nfix n) (len x))
                       (u32-listp x))
                  (u32-listp (update-nth n v x)))
         :hints(("Goal" :in-theory (enable update-nth)))))

(defthm u32-listp-of-smme-mem-clear
  (implies (and (u32-listp (nth *smme-memi* smme))
                (<= (nfix max) (len (nth *smme-memi* smme)))
                (unsigned-byte-p 32 val))
           (u32-listp (nth *smme-memi* (smme-mem-clear n max val smme)))))

(defthm smme-wfp-implies-smme-sizes-okp
  (implies (smme-wfp smme)
           (smme-sizes-okp smme)))

(defun smme-addblock (sz smme)
  (declare (xargs :guard (and (natp sz)
                              (smme-wfp smme))
                  :stobjs smme
                  :guard-hints (("goal" :in-theory (disable smme-wfp
                                                            smme-sizes-okp
                                                            len max resize-list)
                                 :do-not-induct t))))
  (b* ((n (lnfix (smme-nblocks smme)))
       (nstart (smme-block-start n smme))
       (smme (smme-maybe-resize-sizes n smme))
       (smme (smme-maybe-resize-starts (+ 1 n) smme))
       (nsz   (lnfix sz))
       (nextfree (+ nsz nstart))
       (smme (smme-maybe-resize-mem nextfree smme))
       (smme (update-smme-nblocks (+ 1 n) smme))
       (smme (update-smme-blockstartsi (+ 1 n) nextfree smme))
       (smme (update-smme-blocksizesi n nsz smme))
       (smme (smme-mem-clear nstart nextfree 0 smme)))
    smme))

(defthm smme-blocks-wfp-of-incr-nblocks-lemma
  (implies (and (smme-blocks-wfp n smme)
                (<= (nfix n) (nfix (smme-nblocks smme))))
           (smme-blocks-wfp n
                           (UPDATE-NTH
                            *SMME-NBLOCKS*
                            (+ 1 (NFIX (NTH *SMME-NBLOCKS* SMME)))
                            (UPDATE-NTH
                             *SMME-BLOCKSTARTSI*
                             (UPDATE-NTH
                              (+ 1 (NFIX (NTH *SMME-NBLOCKS* SMME)))
                              (+ (NFIX SZ)
                                 (NFIX (NTH (NTH *SMME-NBLOCKS* SMME)
                                            (NTH *SMME-BLOCKSTARTSI* SMME))))
                              (NTH *SMME-BLOCKSTARTSI*
                                   (SMME-MAYBE-RESIZE-STARTS
                                    (+ 1 (NFIX (NTH *SMME-NBLOCKS* SMME)))
                                    (SMME-MAYBE-RESIZE-SIZES (NFIX (NTH *SMME-NBLOCKS* SMME))
                                                            SMME))))
                             (UPDATE-NTH
                              *SMME-BLOCKSIZESI*
                              (UPDATE-NTH (NTH *SMME-NBLOCKS* SMME)
                                          (NFIX SZ)
                                          (NTH *SMME-BLOCKSIZESI*
                                               (SMME-MAYBE-RESIZE-SIZES (NFIX (NTH *SMME-NBLOCKS* SMME))
                                                                       SMME)))
                              (SMME-MAYBE-RESIZE-MEM
                               (+ (NFIX SZ)
                                  (NFIX (NTH (NTH *SMME-NBLOCKS* SMME)
                                             (NTH *SMME-BLOCKSTARTSI* SMME))))
                               (SMME-MAYBE-RESIZE-STARTS
                                (+ 1 (NFIX (NTH *SMME-NBLOCKS* SMME)))
                                (SMME-MAYBE-RESIZE-SIZES (NFIX (NTH *SMME-NBLOCKS* SMME))
                                                        SMME))))))))
  :hints (("goal" :induct (smme-blocks-wfp n smme)
           :expand ((:free (smme) (smme-blocks-wfp n smme)))
           :in-theory (disable nth-with-large-index
                               len-update-nth1))))

(local (defthm equal-nfix-plus-one
         (not (equal (+ 1 (nfix x)) x))
         :hints(("Goal" :in-theory (enable nfix)))))


(defthm smme-wfp-of-smme-addblock
  (implies (smme-wfp smme)
           (smme-wfp (smme-addblock sz smme))))

(defthm smme-addr-of-smme-addblock
  (implies (and (smme-wfp smme)
                (< (nfix n) (nfix (smme-nblocks smme))))
           (equal (smme-addr n i (smme-addblock sz smme))
                  (smme-addr n i smme)))
  :hints(("Goal" :in-theory (enable smme-addr))))

(defthm memi-of-smme-addblock
  (implies (and (< (nfix n) (smme-block-start (smme-nblocks smme) smme))
                (<= (smme-block-start (smme-nblocks smme) smme)
                    (len (nth *smme-memi* smme))))
           (equal (nth n (nth *smme-memi* (smme-addblock sz smme)))
                  (nth n (nth *smme-memi* smme)))))

(defthm smme-read-of-smme-addblock
  (implies (and (smme-wfp smme)
                (< (nfix n) (nfix (smme-nblocks smme)))
                (< (nfix i) (smme-block-size n smme)))
           (equal (smme-read n i (smme-addblock sz smme))
                  (smme-read n i smme)))
  :hints(("Goal" :in-theory (disable smme-addr smme-addblock))))


(defthm smme-read-new-of-smme-addblock
  (implies (and (smme-wfp smme)
                (equal (nfix n) (nfix (smme-nblocks smme)))
                (< (nfix i) (nfix sz)))
           (equal (smme-read n i (smme-addblock sz smme))
                  0))
  :hints(("Goal" :in-theory (enable smme-addr))))

(defthm smme-nblocks-of-smme-addblock
  (equal (smme-nblocks (smme-addblock sz smme))
         (+ 1 (nfix (smme-nblocks smme)))))

(defthm smme-block-size-of-smme-addblock-preserved
  (implies (< (nfix n) (nfix (smme-nblocks smme)))
           (equal (smme-block-size n (smme-addblock sz smme))
                  (smme-block-size n smme))))

(defthm smme-block-size-of-smme-addblock-new
  (equal (smme-block-size (nth *smme-nblocks* smme) (smme-addblock sz smme))
         (nfix sz)))

(defthm true-listp-smme-addblock
  (implies (true-listp smme)
           (true-listp (smme-addblock sz smme))))

(defthm len-smme-addblock
  (implies (equal (len smme) 4)
           (equal (len (smme-addblock sz smme)) 4)))


(local (defthm nat-listp-update-nth
         (implies (and (natp v)
                       (< (nfix n) (len x))
                       (nat-listp x))
                  (nat-listp (update-nth n v x)))
         :hints(("Goal" :in-theory (enable update-nth)))))




(definline smme-clear (smme)
  (declare (xargs :stobjs smme))
  (b* ((smme (update-smme-nblocks 0 smme))
       (smme (smme-maybe-resize-starts 1 smme)))
    (update-smme-blockstartsi 0 0 smme)))

(defthm smme-wfp-of-smme-clear
  (smme-wfp (smme-clear smme)))

(defthm smmep-of-smme-clear
  (implies (smmep smme)
           (smmep (smme-clear smme))))

(defthm nblocks-of-smme-clear
  (equal (nth *smme-nblocks* (smme-clear smme)) 0))


(defmacro def-unguarded (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              . ,decl-body)
            (defun ,name ,formals
              (declare (xargs :guard t))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals)))))))

(def-unguarded smml-nblocks (smm)
  (len smm))

(def-unguarded smml-block-size (n smm)
  (declare (xargs :guard (and (natp n)
                              (< n (smml-nblocks smm)))))
  (len (nth n smm)))

(def-unguarded smml-read (n i smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm)))))
  (nth i (nth n smm)))

(def-unguarded smml-write (n i v smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm))
                              (unsigned-byte-p 32 v))))
  (update-nth n (update-nth i v (nth n smm)) smm))

(def-unguarded smml-addblock (sz smm)
  (declare (xargs :guard (natp sz)))
  (append smm (list (make-list sz :initial-element 0))))

(def-unguarded smml-clear (smm)
  (declare (ignorable smm))
  nil)

(defmacro def-unguarded-rec (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              ,@decls
              ,(subst name-nx name body))
            (defun ,name ,formals
              (declare (xargs :guard t
                              :verify-guards nil))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals))))
            (encapsulate nil
              (local (defthm def-unguarded-identity
                       (equal (,name-nx . ,formals)
                              (,name . ,formals))
                       :hints (("goal" :in-theory
                                '((:induction ,name-nx)
                                  ,name ,name-nx)))))
              (verify-guards ,name)))))

(def-unguarded-rec smml-block-start (n smm)
  (declare (xargs :guard (and (natp n)
                              (<= n (smml-nblocks smm)))))
  (if (or (atom smm)
          (zp n))
      0
    (+ (len (car smm))
       (smml-block-start (1- n) (cdr smm)))))


(def-unguarded smml-max-index (smm)
  (smml-block-start (smml-nblocks smm) smm))

(def-unguarded-rec smml-fast-read (a smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm)))))
  (if (atom smm)
      nil
    (if (< (nfix a) (len (car smm)))
        (nth a (car smm))
      (smml-fast-read (- (nfix a) (len (car smm)))
                     (cdr smm)))))


(defcong nat-equiv equal (smml-fast-read a smm) 1)

(defthm smml-read-in-terms-of-fast-read
  (implies (< (nfix i) (len (nth n smm)))
           (equal (smml-read n i smm)
                  (smml-fast-read (+ (smml-block-start n smm) (nfix i)) smm)))
    :hints(("Goal" :induct t
            :in-theory (enable nth))))


(def-unguarded-rec smml-fast-write (a v smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm))
                              (unsigned-byte-p 32 v))))
  (if (atom smm)
      nil
    (if (< (nfix a) (len (car smm)))
        (cons (update-nth a v (car smm)) (cdr smm))
      (cons (car smm)
            (smml-fast-write (- (nfix a) (len (car smm))) v
                            (cdr smm))))))

(defcong nat-equiv equal (smml-fast-write a v smm) 1)

(defthm smml-write-in-terms-of-fast-write
  (implies (< (nfix i) (len (nth n smm)))
           (equal (smml-write n i v smm)
                  (smml-fast-write (+ (smml-block-start n smm) (nfix i)) v smm)))
  :hints(("Goal" :in-theory (enable nth update-nth)
          :induct t)))

(defun u32-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (u32-listp (car x))
         (u32-list-listp (cdr x)))))

(defthm u32-listp-nth-of-u32-list-listp
  (implies (u32-list-listp x)
           (u32-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))

(defun smmlp (smm)
  (declare (xargs :guard t))
  (u32-list-listp smm))

(defun smml-create ()
  (declare (xargs :guard t))
  nil)

(defthm u32-list-listp-update-nth
  (implies (and (u32-listp v)
                (u32-list-listp x))
           (u32-list-listp (update-nth n v x)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm u32-list-listp-append
  (implies (and (u32-list-listp x)
                (u32-list-listp y))
           (u32-list-listp (append x y))))

(defthm true-list-listp-update-nth
  (implies (and (true-listp v)
                (true-list-listp x))
           (true-list-listp (update-nth n v x)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm true-listp-nth-when-true-list-listp
  (implies (true-list-listp x)
           (true-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))




(defthm true-list-listp-append
  (implies (and (true-list-listp x)
                (true-list-listp y))
           (true-list-listp (append x y))))



(defun-sk smml-smme-blocksizes-ok (smm smme)
  (forall n
          (implies (< (nfix n) (len smm))
                   (equal (nfix (nth n (nth *smme-blocksizesi* smme)))
                          (len (nth n smm)))))
  :rewrite :direct)

(defthm smml-smme-blocksizes-ok-necc2
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (< (nfix n) (len smm))
                (natp (nth n (nth *smme-blocksizesi* smme))))
           (equal (nth n (nth *smme-blocksizesi* smme))
                  (len (nth n smm))))
  :hints (("goal" :use smml-smme-blocksizes-ok-necc
           :in-theory (disable smml-smme-blocksizes-ok-necc
                               smml-smme-blocksizes-ok))))

(defun-sk smml-smme-reads-ok (smm smme)
  (forall (a)
          (implies (< (nfix a) (smml-block-start (len smm) smm))
                   (equal (smml-fast-read a smm)
                          (smme-memi a smme))))
  :rewrite :direct)

(defcong nat-equiv equal (smml-block-start n smm) 1)
(defcong list-equiv equal (smml-block-start n smm) 2
  :hints (("goal" :induct (cdr-cdr-dec-ind smm smm-equiv n)
           :expand ((:with smml-block-start
                     (:free (smm) (smml-block-start n smm)))))))


(defthm smme-blocks-wfp-block-start-bound
  (implies (and (smme-blocks-wfp n smme)
                (< (nfix m) (nfix n)))
           (equal (+ (nfix (nth m (nth *smme-blockstartsi* smme)))
                     (nfix (nth m (nth *smme-blocksizesi* smme))))
                  (nfix (nth (+ 1 (nfix m)) (nth *smme-blockstartsi* smme)))))
  :hints (("goal" :induct (smme-blocks-wfp n smme))))



(defthm smml-block-start-lemma
  (implies (and (natp n) (natp m))
           (equal (smml-block-start (+ n m) smm)
                  (+ (smml-block-start n smm)
                     (smml-block-start m (nthcdr n smm)))))
  :hints (("goal" :induct (smml-block-start n smm))))

(defun smml-block-start-alt-ind (n smm)
  (if (zp n)
      smm
    (smml-block-start-alt-ind (1- n) smm)))

(defthm smml-block-start-alt
  (equal (smml-block-start n smm)
         (if (zp n)
             0
           (+ (smml-block-size (1- n) smm)
              (smml-block-start (1- n) smm))))
  :hints (("goal" :use ((:instance smml-block-start-lemma
                         (n (1- n)) (m 1)))
           :in-theory (disable smml-block-start-lemma)
           :expand ((:free (smm) (smml-block-start 1 smm)))
           :do-not-induct t))
  :rule-classes
  ((:definition :controller-alist ((smml-block-start t nil)))))





(local (defthm smml-block-start-when-smme-blocks-wfp
         (implies (and (smme-blocks-wfp n smme)
                       (equal (smme-block-start 0 smme) 0)
                       (equal (len smm) (nfix (smme-nblocks smme)))
                       (smml-smme-blocksizes-ok smm smme)
                       (<= (nfix m) (nfix n))
                       (<= (nfix m) (nfix (smme-nblocks smme))))
                  (equal (smml-block-start m smm)
                         (smme-block-start m smme)))
         :hints (("goal" :induct (smml-block-start-alt-ind m smm)
                  :in-theory (disable smml-smme-blocksizes-ok
                                      smml-block-start
                                      smme-blocks-wfp-block-start-bound))
                 '(:use ((:instance smme-blocks-wfp-block-start-bound
                          (m (+ -1 m))))))))

(local (defthm smml-block-start-when-smme-wfp
         (implies (and (smml-smme-blocksizes-ok smm smme)
                       (smme-wfp smme)
                       (equal (len smm) (nfix (smme-nblocks smme)))
                       (<= (nfix m) (nfix (smme-nblocks smme))))
                  (equal (smml-block-start m smm)
                         (smme-block-start m smme)))
         :hints (("goal" :use ((:instance smml-block-start-when-smme-blocks-wfp
                                (n (smme-nblocks smme))))))))

(defthm smml-fast-read-when-smme-wfp
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (nfix (smme-nblocks smme)))
                (< (nfix a) (smme-block-start (smme-nblocks smme) smme)))
           (equal (smml-fast-read a smm)
                  (smme-memi a smme)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d ()
                           (smml-smme-blocksizes-ok
                            smml-smme-blocksizes-ok-necc
                            smml-smme-reads-ok
                            smme-blocks-wfp
                            smml-block-start
                            smml-block-start-alt)))))

(encapsulate nil
  (local (defun ind (a1 a2 smm)
           (if (atom smm)
               (list a1 a2)
             (ind (- (nfix a1) (len (car smm)))
                  (- (nfix a2) (len (car smm)))
                  (cdr smm)))))

  (defthm smml-fast-read-of-smml-fast-write-split
    (equal (smml-fast-read a1 (smml-fast-write a2 v smm))
           (if (and (equal (nfix a1) (nfix a2))
                    (< (nfix a2) (smml-block-start (len smm) smm)))
               v
             (smml-fast-read a1 smm)))
    :hints (("goal" :induct (ind a1 a2 smm)
             :in-theory (disable smml-block-start-alt)))))


(defthm true-list-listp-smml-fast-write
  (implies (true-list-listp smm)
           (true-list-listp (smml-fast-write a v smm))))

(defthm u32-list-listp-smml-fast-write
  (implies (and (u32-list-listp smm)
                (unsigned-byte-p 32 v))
           (u32-list-listp (smml-fast-write a v smm))))

(defthm len-smml-fast-write
  (equal (len (smml-fast-write a v smm))
         (len smm)))

(defthm len-nth-smml-fast-write
  (equal (len (nth n (smml-fast-write a v smm)))
         (len (nth n smm)))
  :hints(("Goal" :in-theory (enable nth))))

(defthm smml-smme-blocksizes-ok-of-smml-fast-write-alt
  (implies (smml-smme-blocksizes-ok smm smme)
           (smml-smme-blocksizes-ok (smml-fast-write a v smm) smme))
  :hints (("goal" :in-theory (disable smml-smme-blocksizes-ok)
           :expand ((smml-smme-blocksizes-ok (smml-fast-write a v smm) smme))
           :do-not-induct t)))


(defthm smml-read-is-smme-read
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (equal (len smm) (nfix (smme-nblocks smme)))
                (smme-wfp smme)
                (< (nfix n) (len smm))
                (< (nfix i) (len (nth n smm))))
           (equal (smml-read n i smm)
                  (nth (smme-addr n i smme)
                       (nth *smme-memi* smme))))
  :hints(("Goal" :in-theory (e/d (smme-addr)
                                 (smml-smme-blocksizes-ok
                                  smme-wfp-implies-block-ref-in-bounds
                                  smml-smme-reads-ok
                                  smml-smme-reads-ok-necc
                                  smml-read
                                  smme-wfp))
          :use smme-wfp-implies-block-ref-in-bounds
          :do-not-induct t)))

(defthm smml-addr-in-terms-of-smme-addr
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (equal (len smm) (nfix (smme-nblocks smme)))
                (smme-wfp smme)
                (natp i)
                (< (nfix n) (len smm))
                (< i (len (nth n smm))))
           (equal (+ i (smml-block-start n smm))
                  (smme-addr n i smme)))
  :hints(("Goal" :in-theory (e/d (smme-addr)
                                 (smml-smme-blocksizes-ok
                                  smme-wfp-implies-block-ref-in-bounds
                                  smml-smme-reads-ok
                                  smml-smme-reads-ok-necc
                                  smml-read
                                  smme-wfp))
          :do-not-induct t)))



(defthm smml-block-start-of-smml-fast-write
  (equal (smml-block-start n (smml-fast-write a v smm))
         (smml-block-start n smm))
  :hints(("Goal" :in-theory (e/d (smml-block-start)
                                 (smml-block-start-alt)))))


(defthm smml-smme-reads-ok-of-smml-fast-write-alt
  (implies (smml-smme-reads-ok smm smme)
           (smml-smme-reads-ok (smml-fast-write a v smm)
                             (update-nth *smme-memi*
                                         (update-nth
                                          a v
                                          (nth *smme-memi* smme))
                                         smme)))
  :hints(("Goal" :in-theory (disable smml-smme-reads-ok)
          :expand ((:free (smme) (smml-smme-reads-ok (smml-fast-write a v smm)
                                                  smme)))
          :do-not-induct t)))


(defun smme-nextfree (smme)
  (declare (xargs :stobjs smme
                  :guard (smme-sizes-okp smme)))
  (smme-block-start (smme-nblocks smme) smme))


(defthm smme-addr-in-memi-bounds
  (implies (and (smme-wfp smme)
                (< (nfix n) (nfix (smme-nblocks smme)))
                (< (nfix i) (smme-block-size n smme)))
           (< (smme-addr n i smme) (len (nth *smme-memi* smme))))
  :rule-classes :linear)


(defthm smml-smme-blocksizes-ok-of-addblock
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (nfix (smme-nblocks smme))))
           (smml-smme-blocksizes-ok (append smm (list (make-list-ac sz 0 nil)))
                                  (smme-addblock sz smme)))
  :hints(("Goal" :in-theory (disable smme-wfp
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok
                                     smme-addblock)
          :expand ((smml-smme-blocksizes-ok (append smm (list (make-list-ac sz 0 nil)))
                                          (smme-addblock sz smme)))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:in-theory (disable smme-wfp ;; enable smme-addblock
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok)))))


(defthm smml-block-start-of-addblock
  (equal (smml-block-start (+ 1 (len smm))
                          (append smm (list (make-list-ac sz 0 nil))))
         (+ (nfix sz)
            (smml-block-start (len smm) smm)))
  :hints(("Goal" :in-theory (e/d (smml-block-start)
                                 (smml-block-start-alt
                                  (smml-block-start)))
          :induct (smml-block-start (len smm) smm))))

(encapsulate nil
  (local (defthm smml-fast-read-of-append-split
           (equal (smml-fast-read i (append smm smm2))
                  (if (< (nfix i)
                         (smml-block-start (len smm) smm))
                      (smml-fast-read i smm)
                    (smml-fast-read (- (nfix i)
                                      (smml-block-start (len smm) smm))
                                   smm2)))
           :hints(("Goal" :in-theory (e/d (smml-block-start)
                                          (smml-block-start-alt))))))


  (defthm smml-smme-read-of-addblock
    (implies (and (smml-smme-blocksizes-ok smm smme)
                  (smml-smme-reads-ok smm smme)
                  (smme-wfp smme)
                  (equal (len smm) (nfix (smme-nblocks smme)))
                  (< (nfix i) (smml-block-start
                               (+ 1 (len smm))
                               (append smm (list (make-list-ac sz 0 nil))))))
             (equal (smml-fast-read i (append smm (list (make-list-ac sz 0 nil))))
                    (smme-memi i (smme-addblock sz smme))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable smml-smme-blocksizes-ok
                                 smml-smme-reads-ok)))))


(defthm smml-smme-reads-ok-of-addblock
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (nfix (smme-nblocks smme))))
           (smml-smme-reads-ok (append smm (list (make-list-ac sz 0 nil)))
                             (smme-addblock sz smme)))
  :hints(("Goal" :in-theory (disable smme-wfp
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok
                                     smme-addblock
                                     smml-smme-blocksizes-ok-of-addblock)
          :expand ((smml-smme-reads-ok (append smm (list (make-list-ac sz 0 nil)))
                                     (smme-addblock sz smme)))
          :use smml-smme-blocksizes-ok-of-addblock
          :do-not-induct t)))


(defthm nfix-of-decr-less-than
  (implies (natp x)
           (equal (< (nfix (+ -1 x)) x)
                  (not (equal x 0)))))

(defthm smml-block-start-lte-len-memi
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smme-wfp smme)
                (equal (len smm)
                       (nfix (smme-nblocks smme))))
           (<= (smml-block-start (len smm) smm)
               (len (nth *smme-memi* smme))))
  :hints(("Goal" :in-theory (e/d (smme-addr)
                                 (smml-smme-blocksizes-ok
                                  nth-with-large-index))
          :do-not-induct t
          :use ((:instance smme-addr-in-memi-bounds
                 (n (1- (nfix (smme-nblocks smme))))
                 (i (1- (smme-block-size (1- (nfix (smme-nblocks smme))) smme))))
                (:instance smme-blocks-wfp-block-start-bound
                 (m (+ -1 (len smm)))
                 (n (len smm))))))
  :rule-classes :linear)

(defthm smme-wfp-of-update-memi
  (implies (smme-wfp smme)
           (smme-wfp (update-nth *smme-memi*
                                (update-nth i v (nth *smme-memi* smme))
                                smme))))

(defthm u32-listp-of-make-list-ac
  (implies (and (u32-listp acc)
                (unsigned-byte-p 32 default))
           (u32-listp (make-list-ac sz default acc))))

(encapsulate nil
  (local
   (progn


     (defun-nx smme-corr (smme smm)
       (and (true-list-listp smm)
            (smme-wfp smme)
            (smmep smme)
            (equal (len smm) (nfix (smme-nblocks smme)))
            (smml-smme-blocksizes-ok smm smme)
            (smml-smme-reads-ok smm smme)))))

  (local (in-theory (disable (smme-corr)
                             (force)
                             smme-wfp
                             smme-clear
                             smml-read (smml-read)
                             smme-write (smme-write)
                             smme-read (smme-read)
                             smml-smme-blocksizes-ok
                             smml-smme-reads-ok
                             smme-addblock
                             smml-read-in-terms-of-fast-read
                             smml-block-start-when-smme-wfp
                             smmep
                             ; smme-addr-in-terms-of-smml-block-start
                             smml-block-start-when-smme-blocks-wfp)))

  (local (set-default-hints '('(:do-not-induct t)
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smmep)))
                              (and stable-under-simplificationp
                                   (let ((lit (car (last clause))))
                                     (and (member (car lit) '(smml-smme-reads-ok
                                                              smml-smme-blocksizes-ok))
                                          `(:expand (,lit)))))
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smme-read
                                                        ; smme-addr-in-terms-of-smml-block-start
                                                        smme-write)))
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smme-addblock
                                                        smml-block-start-when-smme-wfp)))
                              )))


  (defabsstobj-events smm
    :concrete smme
    :recognizer (smmp :logic smmlp :exec smmep)
    :creator (smm-create :logic smml-create :exec create-smme)
    :corr-fn smme-corr
    :exports ((smm-nblocks :logic smml-nblocks :exec smme-nblocks)
              (smm-block-size :logic smml-block-size :exec smme-block-size$inline)
              (smm-read :logic smml-read :exec smme-read$inline)
              (smm-write :logic smml-write :exec smme-write$inline)
              (smm-addblock :logic smml-addblock :exec smme-addblock
                            :protect t)
              (smm-clear :logic smml-clear :exec smme-clear$inline
                         :protect t)
              (smm-block-start :logic smml-block-start :exec smme-block-start$inline)
              (smm-max-index :logic smml-max-index :exec smme-nextfree)
              (smm-fast-read :logic smml-fast-read :exec smme-memi)
              (smm-fast-write :logic smml-fast-write :exec update-smme-memi)))

  ;; note it's doing the proofs all over again here, we should do something
  ;; about this
  (defabsstobj-events smm2
    :concrete smme
    :recognizer (smm2p :logic smmlp :exec smmep)
    :creator (smm2-create :logic smml-create :exec create-smme)
    :corr-fn smme-corr
    :exports ((smm2-nblocks :logic smml-nblocks :exec smme-nblocks)
              (smm2-block-size :logic smml-block-size :exec smme-block-size$inline)
              (smm2-read :logic smml-read :exec smme-read$inline)
              (smm2-write :logic smml-write :exec smme-write$inline)
              (smm2-addblock :logic smml-addblock :exec smme-addblock
                             :protect t)
              (smm2-clear :logic smml-clear :exec smme-clear$inline
                          :protect t)
              (smm2-block-start :logic smml-block-start :exec smme-block-start$inline)
              (smm2-max-index :logic smml-max-index :exec smme-nextfree)
              (smm2-fast-read :logic smml-fast-read :exec smme-memi)
              (smm2-fast-write :logic smml-fast-write :exec update-smme-memi))
    :congruent-to smm)

  (defabsstobj-events smm3
    :concrete smme
    :recognizer (smm3p :logic smmlp :exec smmep)
    :creator (smm3-create :logic smml-create :exec create-smme)
    :corr-fn smme-corr
    :exports ((smm3-nblocks :logic smml-nblocks :exec smme-nblocks)
              (smm3-block-size :logic smml-block-size :exec smme-block-size$inline)
              (smm3-read :logic smml-read :exec smme-read$inline)
              (smm3-write :logic smml-write :exec smme-write$inline)
              (smm3-addblock :logic smml-addblock :exec smme-addblock
                             :protect t)
              (smm3-clear :logic smml-clear :exec smme-clear$inline
                          :protect t)
              (smm3-block-start :logic smml-block-start :exec smme-block-start$inline)
              (smm3-max-index :logic smml-max-index :exec smme-nextfree)
              (smm3-fast-read :logic smml-fast-read :exec smme-memi)
              (smm3-fast-write :logic smml-fast-write :exec update-smme-memi))
    :congruent-to smm))









