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
(include-book "litp")
(include-book "centaur/misc/arrays" :dir :system)
(include-book "std/stobjs/bitarr" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(fty::deflist bit-list :pred bit-listp :elt-type bit :true-listp t)

(defthm bitarr$ap-is-bit-listp
  (equal (acl2::bitarr$ap x)
         (bit-listp x)))

;; might be useful for memo tables in places
;; (defsection nth-id

;;   (defund nth-id (n x)
;;     (id-fix (nth n x)))

;;   (local (in-theory (enable nth-id)))

;;   (defcong nat-equiv equal (nth-id n x) 1)

;;   (defthm idp-of-nth-id
;;     (idp (nth-id n x)))

;;   (defund update-nth-id (n v x)
;;     (update-nth n (id-fix v) x))

;;   (defthm nth-id-of-resize-list
;;     (implies (<= (len lst) (nfix m))
;;              (equal (nth-id n (resize-list lst m 0))
;;                     (nth-id n lst)))
;;     :hints(("Goal" :in-theory (enable ;; nth-node
;;                                acl2::nth-with-large-index
;;                                acl2::nth-of-resize-list-split))))

;;   (local (in-theory (enable update-nth-id)))

;;   (defcong nat-equiv equal (update-nth-id n v x) 1)
;;   (defcong id-equiv equal (update-nth-id n v x) 2)

;;   (defthm nth-id-of-update-nth-id-same
;;     (equal (nth-id n (update-nth-id n v x))
;;            (id-fix v)))

;;   (defthm nth-id-of-update-nth-id-diff
;;     (implies (not (equal (nfix n) (nfix m)))
;;              (equal (nth-id m (update-nth-id n v x))
;;                     (nth-id m x))))

;;   (defthm nth-id-of-update-nth-id-split
;;     (equal (nth-id m (update-nth-id n v x))
;;            (if (equal (nfix n) (nfix m))
;;                (id-fix v)
;;              (nth-id m x))))

;;   (defthm len-update-nth-id-not-smaller
;;     (<= (len x) (len (update-nth-id n v x)))
;;     :rule-classes (:rewrite :linear))

;;   (defthm len-update-nth-id-at-least-n
;;     (<= (nfix n) (len (update-nth-id n v x)))
;;     :rule-classes (:rewrite :linear))

;;   (defthm update-nth-id-same
;;     (equal (update-nth-id n v1 (update-nth-id n v2 arr))
;;            (update-nth-id n v1 arr)))

;;   (defthmd update-nth-id-switch
;;     (implies (not (equal (nfix n1) (nfix n2)))
;;              (equal (update-nth-id n2 v2 (update-nth-id n1 v1 l))
;;                     (update-nth-id n1 v1 (update-nth-id n2 v2 l))))
;;     :rule-classes ((:rewrite :loop-stopper ((n2 n1))))))

(defsection nth-lit

  (defund nth-lit (n x)
    (lit-fix (nth n x)))

  (local (in-theory (enable nth-lit)))

  (defcong nat-equiv equal (nth-lit n x) 1)

  (defthm litp-of-nth-lit
    (litp (nth-lit n x)))

  (defthm nth-lit-of-resize-list
    (implies (<= (len lst) (nfix m))
             (equal (nth-lit n (resize-list lst m 0))
                    (nth-lit n lst)))
    :hints(("Goal" :in-theory (enable ;; nth-node
                               acl2::nth-with-large-index
                               acl2::nth-of-resize-list-split))))

  (defund update-nth-lit (n v x)
    (update-nth n (lit-fix v) x))
  (local (in-theory (enable update-nth-lit)))

  (defcong nat-equiv equal (update-nth-lit n v x) 1)
  (defcong lit-equiv equal (update-nth-lit n v x) 2)

  (defthm nth-lit-of-update-nth-lit-same
    (equal (nth-lit n (update-nth-lit n v x))
           (lit-fix v)))

  (defthm nth-lit-of-update-nth-lit-diff
    (implies (not (equal (nfix n) (nfix m)))
             (equal (nth-lit m (update-nth-lit n v x))
                    (nth-lit m x))))

  (defthm nth-lit-of-update-nth-lit-split
    (equal (nth-lit m (update-nth-lit n v x))
           (if (equal (nfix n) (nfix m))
               (lit-fix v)
             (nth-lit m x))))

  (defthm len-update-nth-lit-not-smaller
    (<= (len x) (len (update-nth-lit n v x)))
    :rule-classes (:rewrite :linear))

  (defthm len-update-nth-lit-at-least-n+1
    (<= (+ 1 (nfix n)) (len (update-nth-lit n v x)))
    :rule-classes ((:linear :trigger-terms ((len (update-nth-lit n v x))))))

  (defthm len-of-update-nth-lit
    (implies (< (nfix n) (len x))
             (equal (len (update-nth-lit n val x))
                    (len x)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defthm update-nth-lit-same
    (equal (update-nth-lit n v1 (update-nth-lit n v2 arr))
           (update-nth-lit n v1 arr)))

  (defthmd update-nth-lit-switch
    (implies (not (equal (nfix n1) (nfix n2)))
             (equal (update-nth-lit n2 v2 (update-nth-lit n1 v1 l))
                    (update-nth-lit n1 v1 (update-nth-lit n2 v2 l))))
    :rule-classes ((:rewrite :loop-stopper ((n2 n1))))))

;; (defsection indices-in-bounds
;;   ;; predicate for saying that a memo table is large enough for an aignet
;;   ;; Each type of memo table will have a different executable predicate, but
;;   ;; they all rewrite to this one, which the in-bounds rewrite rule triggers on.
;;   (defund-nx memo-tablep (arr aignet)
;;     (<= (nfix (num-fanins aignet)) (len arr)))

;;   (local (in-theory (enable memo-tablep)))

;;   (defund-nx id-in-bounds (n arr)
;;     (< (nfix n) (len arr)))

;;   (defund-nx iterator-in-bounds (n arr)
;;     (<= (nfix n) (len arr)))

;;   (local (in-theory (enable id-in-bounds
;;                             iterator-in-bounds)))

;;   (defcong nat-equiv equal (id-in-bounds n arr) 1)
;;   (defcong nat-equiv equal (iterator-in-bounds n arr) 1)

;;   (defthm less-than-len-when-id-in-bounds
;;     (implies (double-rewrite (id-in-bounds n arr))
;;              (< (nfix n) (len arr)))
;;     :hints(("Goal" :in-theory (enable aignet-idp))))

;;   (defthm id-in-bounds-when-memo-tablep
;;     (implies (and (memo-tablep arr aignet)
;;                   (double-rewrite (aignet-idp n aignet)))
;;              (id-in-bounds n arr))
;;     :hints(("Goal" :in-theory (enable aignet-idp))))

;;   (defthm iterator-in-bounds-when-memo-tablep
;;     (implies (and (memo-tablep arr aignet)
;;                   (<= (nfix n) (+ 1 (fanin-count aignet))))
;;              (iterator-in-bounds n arr)))

;;   (defthm id-in-bounds-of-update
;;     (implies (id-in-bounds n arr)
;;              (id-in-bounds n (update-nth m v arr))))

;;   ;; (defthm id-in-bounds-of-update-nth-id
;;   ;;   (implies (id-in-bounds n arr)
;;   ;;            (id-in-bounds n (update-nth-id m v arr)))
;;   ;;   :hints(("Goal" :in-theory (enable update-nth-id))))

;;   (defthm id-in-bounds-of-update-nth-lit
;;     (implies (id-in-bounds n arr)
;;              (id-in-bounds n (update-nth-lit m v arr)))
;;     :hints(("Goal" :in-theory (enable update-nth-lit))))

;;   (defthm memo-tablep-when-big-enough
;;     (implies (<= (nfix (num-fanins aignet)) (len arr))
;;              (memo-tablep arr aignet)))

;;   (defthm memo-tablep-of-update-nth
;;     (implies (memo-tablep arr aignet)
;;              (memo-tablep (update-nth n v arr) aignet)))

;;   ;; (defthm memo-tablep-of-update-nth-id
;;   ;;   (implies (memo-tablep arr aignet)
;;   ;;            (memo-tablep (update-nth-id n v arr) aignet))
;;   ;;   :hints(("Goal" :in-theory (enable update-nth-id))))

;;   (defthm memo-tablep-of-update-nth-lit
;;     (implies (memo-tablep arr aignet)
;;              (memo-tablep (update-nth-lit n v arr) aignet))
;;     :hints(("Goal" :in-theory (enable update-nth-lit))))

;;   (defthm iterator-in-bounds-of-update
;;     (implies (iterator-in-bounds n arr)
;;              (iterator-in-bounds n (update-nth m v arr))))

;;   ;; (defthm iterator-in-bounds-of-update-nth-id
;;   ;;   (implies (iterator-in-bounds n arr)
;;   ;;            (iterator-in-bounds n (update-nth-id m v arr)))
;;   ;;   :hints(("Goal" :in-theory (enable update-nth-id))))

;;   (defthm iterator-in-bounds-of-update-nth-lit
;;     (implies (iterator-in-bounds n arr)
;;              (iterator-in-bounds n (update-nth-lit m v arr)))
;;     :hints(("Goal" :in-theory (enable update-nth-lit))))

;;   (defthm big-enough-when-memo-tablep
;;     (implies (memo-tablep arr aignet)
;;              (< (fanin-count aignet) (len arr)))
;;     :rule-classes (:rewrite :forward-chaining))

;;   (defthm id-in-bounds-when-iterator-in-bounds-and-less
;;     (implies (and (iterator-in-bounds n arr)
;;                   (not (equal (nfix n) (len arr))))
;;              (id-in-bounds n arr)))

;;   (defthm id-in-bounds-of-one-less
;;     (implies (and (iterator-in-bounds n arr)
;;                   (not (zp n)))
;;              (id-in-bounds (+ -1 n) arr)))

;;   (defthm iterator-in-bounds-of-incr
;;     (implies (and (iterator-in-bounds n arr)
;;                   (not (equal (nfix n) (len arr))))
;;              (iterator-in-bounds (+ 1 (nfix n)) arr)))

;;   (defthm iterator-in-bounds-of-incr-nat
;;     (implies (and (iterator-in-bounds n arr)
;;                   (natp n)
;;                   (not (equal n (len arr))))
;;              (iterator-in-bounds (+ 1 n) arr)))

;;   (defthm iterator-in-bounds-of-decr
;;     (implies (and (iterator-in-bounds n arr)
;;                   (not (zp n)))
;;              (iterator-in-bounds (+ -1 n) arr))))

;; (defsection aignet-iterator-p
;;   (defund aignet-iterator-p (n aignet)
;;     (declare (xargs :stobjs aignet
;;                     :guard (natp n)))
;;     (<= (lnfix n) (lnfix (num-fanins aignet))))

;;   (local (in-theory (enable aignet-iterator-p)))

;;   (defthm aignet-idp-when-iterator-and-less
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (not (equal (nfix n) (nfix (num-fanins aignet)))))
;;              (aignet-idp n aignet))
;;     :hints(("Goal" :in-theory (enable aignet-idp))))

;;   (defthm aignet-idp-of-one-less
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (not (zp n)))
;;              (aignet-idp (+ -1 n) aignet)))

;;   (defthm aignet-iterator-p-of-zero
;;     (aignet-iterator-p 0 aignet))

;;   (defthm aignet-iterator-p-of-num-fanins
;;     (aignet-iterator-p (+ 1 (fanin-count aignet)) aignet))

;;   (defthm aignet-iterator-p-of-incr
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (not (equal (nfix n) (+ 1 (fanin-count aignet)))))
;;              (aignet-iterator-p (+ 1 (nfix n)) aignet)))

;;   (defthm aignet-iterator-p-of-incr-nat
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (natp n)
;;                   (not (equal n (+ 1 (fanin-count aignet)))))
;;              (aignet-iterator-p (+ 1 n) aignet)))

;;   (defthm aignet-iterator-p-of-decr
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (not (zp n)))
;;              (aignet-iterator-p (+ -1 n) aignet)))

;;   (defthm aignet-iterator-p-implies-less
;;     (implies (and (aignet-iterator-p n aignet)
;;                   (integerp n)
;;                   (not (equal n (+ 1 (fanin-count aignet)))))
;;              (<= n (fanin-count aignet))))

;;   (defthmd aignet-iterator-p-when-lte
;;     (implies (and (<= x (+ 1 (fanin-count aignet)))
;;                   (integerp x))
;;              (aignet-iterator-p x aignet))
;;     :hints(("Goal" :in-theory (enable aignet-iterator-p)))))


(defsection bitarr
  ;; bug workaround
  ;; (in-theory (disable (acl2::bitarrp)))
  ;; (defun bitarr-sizedp (bitarr aignet)
  ;;   (declare (xargs :stobjs (bitarr aignet)
  ;;                   :guard-hints ('(:in-theory (e/d (memo-tablep))))))
  ;;   (mbe :logic (non-exec (memo-tablep bitarr aignet))
  ;;        :exec (<= (num-fanins aignet) (bits-length bitarr))))

  ;; (defun bitarr-id-in-bounds (id bitarr)
  ;;   (declare (xargs :guard (idp id)
  ;;                   :stobjs bitarr
  ;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  ;;   (mbe :logic (non-exec (id-in-bounds id bitarr))
  ;;        :exec (< (id-val id) (bits-length bitarr))))

  ;; (defun bitarr-iterator-in-bounds (n bitarr)
  ;;   (declare (xargs :guard (natp n)
  ;;                   :stobjs bitarr
  ;;                   :guard-hints (("goal" :in-theory (e/d (iterator-in-bounds))))))
  ;;   (mbe :logic (non-exec (iterator-in-bounds n bitarr))
  ;;        :exec (<= (nfix n) (bits-length bitarr))))

  ;; (definline get-id->bit (id bitarr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs bitarr
  ;;                   :guard (and (idp id)
  ;;                               (bitarr-id-in-bounds id bitarr))))
  ;;   (get-bit (id-val id) bitarr))

  ;; (definline set-id->bit (id v bitarr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs bitarr
  ;;                   :guard (and (idp id)
  ;;                               (bitp v)
  ;;                               (bitarr-id-in-bounds id bitarr))))
  ;;   (set-bit (id-val id) v bitarr))

  (local (in-theory (enable resize-list)))

  (definline bitarr-clear (bitarr)
    (declare (xargs :stobjs bitarr
                    :guard-hints ('(:expand ((len bitarr)
                                             (len (cdr bitarr)))
                                    :in-theory (e/d (nth update-nth))))))
    (mbe :logic (non-exec nil)
         :exec (resize-bits 0 bitarr))))



(defsection litarr
  (acl2::def-1d-arr litarr
                    :slotname lit
                    :pred litp
                    :fix satlink::lit-fix$inline
                    :type-decl (unsigned-byte 32)
                    :default-val 0
                    :rename ((get-lit . get-lit_)
                             (set-lit . set-lit_)))

  (definline get-lit (n litarr)
    (declare (xargs :stobjs litarr
                    :guard (and (natp n)
                                (< n (lits-length litarr)))
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    (mbe :logic (non-exec (nth-lit n litarr))
         :exec (get-lit_ n litarr)))

  (definline set-lit (n v litarr)
    (declare (xargs :stobjs litarr
                    :guard (and (natp n)
                                (< n (lits-length litarr))
                                (litp v))
                    :guard-hints ('(:in-theory (enable update-nth-lit)))))
    (mbe :logic (non-exec (update-nth-lit n (lit-fix v) litarr))
         :exec (if (< (the (integer 0 *) v) (expt 2 32))
                   (set-lit_ n v litarr)
                 (ec-call (set-lit_ n v litarr)))))

  ;; (defun litarr-sizedp (litarr aignet)
  ;;   (declare (xargs :stobjs (litarr aignet)
  ;;                   :guard-hints ('(:in-theory (enable memo-tablep)))))
  ;;   (mbe :logic (non-exec (memo-tablep litarr aignet))
  ;;        :exec (<= (num-fanins aignet) (lits-length litarr))))

  ;; (defun litarr-id-in-bounds (id litarr)
  ;;   (declare (xargs :guard (idp id)
  ;;                   :stobjs litarr
  ;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  ;;   (mbe :logic (non-exec (id-in-bounds id litarr))
  ;;        :exec (< (id-val id) (lits-length litarr))))

  ;; (defun litarr-iterator-in-bounds (n litarr)
  ;;   (declare (xargs :guard (natp n)
  ;;                   :stobjs litarr
  ;;                   :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
  ;;   (mbe :logic (non-exec (iterator-in-bounds n litarr))
  ;;        :exec (<= (nfix n) (lits-length litarr))))


  ;; (local (in-theory (enable nth-lit update-nth-lit)))

  ;; (local (in-theory (enable nth-lit nth-id
  ;;                           update-nth-lit update-nth-id
  ;;                           id-in-bounds)))

  ;; ;; using a litarr as various types of mapping
  ;; (definline get-id->lit (id litarr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs litarr
  ;;                   :guard (and (idp id)
  ;;                               (litarr-id-in-bounds id litarr))))
  ;;   (get-lit (id-val id) litarr))

  ;; (definline set-id->lit (id lit litarr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (type (integer 0 *) lit)
  ;;            (xargs :stobjs litarr
  ;;                   :guard (and (idp id) (litp lit)
  ;;                               (litarr-id-in-bounds id litarr))))
  ;;   (set-lit (id-val id) lit litarr))

  (local (in-theory (enable resize-list)))

  (definline litarr-clear (litarr)
    (declare (xargs :stobjs litarr
                    :guard-hints ('(:expand ((len litarr)
                                             (len (cdr litarr)))
                                    :in-theory (enable nth update-nth)))))
    (mbe :logic (non-exec nil)
         :exec (resize-lits 0 litarr)))

  (acl2::def-universal-equiv
   lits-equiv
   :qvars (i)
   :equiv-terms ((lit-equiv (nth i x))))

  (defcong lits-equiv lit-equiv (nth i x) 2
    :hints ('(:use ((:instance lits-equiv-necc
                     (acl2::y x-equiv))))))
  (defcong lits-equiv lits-equiv (update-nth i v x) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable lits-equiv-necc)))))
  (defcong lit-equiv lits-equiv (update-nth i v x) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable lits-equiv-necc)))))

  (local (in-theory (enable nth-lit update-nth-lit)))

  (defcong lits-equiv lit-equiv (nth-lit i x) 2)
  (defcong lits-equiv lits-equiv (update-nth-lit i v x) 3)
  (defcong lit-equiv lits-equiv (update-nth-lit i v x) 2))

;; (defsection idarr
;;   (acl2::def-1d-arr :arrname idarr
;;                     :slotname id
;;                     :pred idp
;;                     :fix id-fix$inline
;;                     :type-decl (unsigned-byte 32)
;;                     :default-val 0
;;                     :rename ((get-id . get-id_)
;;                              (set-id . set-id_)))

;;   (definline get-id (n idarr)
;;     (declare (xargs :stobjs idarr
;;                     :guard (and (natp n)
;;                                 (< n (ids-length idarr)))
;;                     :guard-hints ('(:in-theory (enable nth-id)))))
;;     (mbe :logic (non-exec (nth-id n idarr))
;;          :exec (get-id_ n idarr)))

;;   (definline set-id (n v idarr)
;;     (declare (xargs :stobjs idarr
;;                     :guard (and (natp n)
;;                                 (< n (ids-length idarr))
;;                                 (idp v))
;;                     :guard-hints ('(:in-theory (enable update-nth-id)))))
;;     (mbe :logic (non-exec (update-nth-id n (id-fix v) idarr))
;;          :exec (if (< (the (integer 0 *) v) (expt 2 32))
;;                    (set-id_ n v idarr)
;;                  (ec-call (set-id_ n v idarr)))))

;;   (defun idarr-sizedp (idarr aignet)
;;     (declare (xargs :stobjs (idarr aignet)
;;                     :guard-hints ('(:in-theory (enable memo-tablep)))))
;;     (mbe :logic (non-exec (memo-tablep idarr aignet))
;;          :exec (<= (num-fanins aignet) (ids-length idarr))))

;;   (defun idarr-id-in-bounds (id idarr)
;;     (declare (xargs :guard (idp id)
;;                     :stobjs idarr
;;                     :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
;;     (mbe :logic (non-exec (id-in-bounds id idarr))
;;          :exec (< (id-val id) (ids-length idarr))))

;;   (defun idarr-iterator-in-bounds (n idarr)
;;     (declare (xargs :guard (natp n)
;;                     :stobjs idarr
;;                     :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
;;     (mbe :logic (non-exec (iterator-in-bounds n idarr))
;;          :exec (<= (nfix n) (ids-length idarr))))

;;   (local (in-theory (enable nth-id update-nth-id)))

;;   ;; (defthm idp-nth-in-idsp
;;   ;;   (implies (and (idsp arr)
;;   ;;                 (< (nfix n) (len arr)))
;;   ;;            (idp (nth n arr)))
;;   ;;   :hints(("Goal" :in-theory (enable nth))))

;;   ;; (definline get-id (n idarr)
;;   ;;   (declare (type (integer 0 *) n)
;;   ;;            (xargs :stobjs idarr
;;   ;;                   :guard (< n (ids-length idarr))))
;;   ;;   (mbe :logic (non-exec (nth-id n idarr))
;;   ;;        :exec (idsi n idarr)))

;;   ;; (definline set-id (n v idarr)
;;   ;;   (declare (type (integer 0 *) n)
;;   ;;            (type (integer 0 *) v)
;;   ;;            (xargs :stobjs idarr
;;   ;;                   :guard (and (< n (ids-length idarr))
;;   ;;                               (idp v))))
;;   ;;   (mbe :logic (non-exec   ;;                                     (update-nth-id
;;   ;;                                      n (id-fix v)
;;   ;;                                      (nth *idsi* idarr))
;;   ;;                                     idarr))
;;   ;;        :exec (if (< v (expt 2 32))
;;   ;;                  (update-idsi n v idarr)
;;   ;;                (ec-call (update-idsi n v idarr)))))

;;   (local (in-theory (enable nth-id nth-id
;;                             update-nth-id update-nth-id
;;                             id-in-bounds)))
;;   ;; using a idarr as various types of mapping
;;   (definline get-id->id (id idarr)
;;     (declare (type (integer 0 *) id)
;;              (xargs :stobjs idarr
;;                     :guard (and (idp id)
;;                                 (idarr-id-in-bounds id idarr))))
;;     (get-id (id-val id) idarr))

;;   (definline set-id->id (id idv idarr)
;;     (declare (type (integer 0 *) id)
;;              (type (integer 0 *) id)
;;              (xargs :stobjs idarr
;;                     :guard (and (idp id) (idp idv)
;;                                 (idarr-id-in-bounds id idarr))))
;;     (set-id (id-val id) idv idarr))

;;   (acl2::def-universal-equiv
;;    ids-equiv
;;    :qvars (i)
;;    :equiv-terms ((nat-equiv (nth i x))))

;;   (defcong ids-equiv nat-equiv (nth i x) 2
;;     :hints ('(:use ((:instance ids-equiv-necc
;;                      (acl2::y x-equiv))))))
;;   (defcong ids-equiv ids-equiv (update-nth i v x) 3
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))
;;                    :in-theory (enable ids-equiv-necc)))))
;;   (defcong nat-equiv ids-equiv (update-nth i v x) 2
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))
;;                    :in-theory (enable ids-equiv-necc)))))

;;   (local (in-theory (enable nth-id update-nth-id)))

;;   (defcong ids-equiv nat-equiv (nth-id i x) 2)
;;   (defcong ids-equiv ids-equiv (update-nth-id i v x) 3)
;;   (defcong nat-equiv ids-equiv (update-nth-id i v x) 2))

(defsection u32arr

  (acl2::def-1d-arr u32arr
                    :slotname u32
                    :pred natp
                    :fix nfix
                    :type-decl (unsigned-byte 32)
                    :default-val 0
                    :rename ((set-u32 . set-u32_)
                             (u32s-length . u32-length)
                             (resize-u32s . resize-u32)))

  (defun set-u32-ec-call (n v u32arr)
    (declare (xargs :stobjs u32arr
                    :guard t))
    (ec-call (set-u32_ n v u32arr)))

  (definline set-u32 (n v u32arr)
    (declare (xargs :stobjs u32arr
                    :guard (and (natp n)
                                (< n (u32-length u32arr))
                                (natp v))))
    (mbe :logic (set-u32_ n (nfix v) u32arr)
         :exec (if (< (the (integer 0 *) v) (expt 2 32))
                   (set-u32_ n v u32arr)
                 (set-u32-ec-call n v u32arr))))

  ;; (defun u32arr-sizedp (u32arr aignet)
  ;;   (declare (xargs :stobjs (u32arr aignet)
  ;;                   :guard-hints ('(:in-theory (enable memo-tablep)))))
  ;;   (mbe :logic (non-exec (memo-tablep u32arr aignet))
  ;;        :exec (<= (num-fanins aignet) (u32-length u32arr))))

  ;; (defun u32arr-id-in-bounds (id u32arr)
  ;;   (declare (xargs :guard (idp id)
  ;;                   :stobjs u32arr
  ;;                   :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
  ;;   (mbe :logic (non-exec (id-in-bounds id u32arr))
  ;;        :exec (< (id-val id) (u32-length u32arr))))

  ;; (defun u32arr-iterator-in-bounds (n u32arr)
  ;;   (declare (xargs :guard (natp n)
  ;;                   :stobjs u32arr
  ;;                   :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
  ;;   (mbe :logic (non-exec (iterator-in-bounds n u32arr))
  ;;        :exec (<= (nfix n) (u32-length u32arr))))

  ;; ;; (defthm u32p-is-32bit-listp
  ;; ;;   (equal (u32p x)
  ;; ;;          (32bit-listp x)))

  ;; (local (in-theory (enable nth-lit nth-id
  ;;                           update-nth-lit update-nth-id
  ;;                           id-in-bounds)))

  ;; (definline get-id->nat (id u32arr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs u32arr
  ;;                   :guard (and (idp id)
  ;;                               (u32arr-id-in-bounds id u32arr))))
  ;;   (lnfix (get-u32 (id-val id) u32arr)))

  ;; (definline set-id->nat (id n u32arr)
  ;;   (declare (type (integer 0 *) id)
  ;;            (type (integer 0 *) n)
  ;;            (xargs :stobjs u32arr
  ;;                   :guard (and (idp id)
  ;;                               (u32arr-id-in-bounds id u32arr))))
  ;;   (set-u32 (id-val id) (lnfix n) u32arr))
  )



(defstobj-clone mark bitarr :suffix "-MARK")
(defstobj-clone copy litarr :prefix "COPY")
(defstobj-clone vals bitarr :prefix "VALS")
