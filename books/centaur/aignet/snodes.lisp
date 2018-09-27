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
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "misc/definline" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))


(defsection snode-accessors

  ;; get a single field from a particular slot. Some of these are not strictly
  ;; guarded because the slot doesn't contain all the type information, but the
  ;; corresponding rewrite rules won't fire unless it is established, so the
  ;; error should show up fairly quickly.
  (definlined snode->type (slot0)
    (declare (type (integer 0 *) slot0))
    (mbe :logic (logand 3 (lnfix slot0))
         :exec (if (<= slot0 #xffffffff)
                   (logand 3 (the (unsigned-byte 32) slot0))
                 (logand 3 slot0))))

  (defthm snode->type-natp
    (natp (snode->type slot0))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (snode->type slot) 1
    :hints(("Goal" :in-theory (enable snode->type))))

  (define snode->type^ ((slot0 :type (unsigned-byte 32)))
    :inline t
    :enabled t
    :guard-hints (("goal" :in-theory (enable snode->type)))
    (mbe :logic (snode->type slot0)
         :exec (logand 3 (the (unsigned-byte 32) slot0))))

  (defthm snode->type-bound
    (< (snode->type slot0) 4)
    :hints(("Goal" :in-theory (enable snode->type)
            :expand ((:free (m) (acl2::loghead 2 m))
                     (:free (m) (acl2::loghead 1 m))
                     (:free (m) (acl2::loghead 0 m)))))
    :rule-classes :linear)

  (definlined snode->phase (slot1)
    (declare (type (integer 0 *) slot1))
    (mbe :logic (logand 1 (ash (lnfix slot1) -1))
         :exec (if (<= slot1 #xffffffff)
                   (logand 1 (the (unsigned-byte 32)
                                  (ash (the (unsigned-byte 32) slot1) -1)))
                 (logand 1 (ash (lnfix slot1) -1)))))

  (define snode->phase^ ((slot1 :type (unsigned-byte 32)))
    :inline t
    :enabled t
    :guard-hints (("goal" :in-theory (enable snode->phase)))
    (mbe :logic (snode->phase slot1)
         :exec (logand 1 (the (unsigned-byte 32)
                                  (ash (the (unsigned-byte 32) slot1) -1)))))

  (defcong nat-equiv equal (snode->phase slot) 1
    :hints(("Goal" :in-theory (enable snode->phase))))

  (defthm bitp-snode->phase
    (bitp (snode->phase slot1))
    :hints(("Goal" :in-theory (enable snode->phase))))

  (definlined snode->regp (slot1)
    (declare (type (integer 0 *) slot1))
    (mbe :logic (logand 1 (lnfix slot1))
         :exec (if (<= slot1 #xffffffff)
                   (logand 1 (the (unsigned-byte 32) slot1))
                 (logand 1 (lnfix slot1)))))

  (define snode->regp^ ((slot1 :type (unsigned-byte 32)))
    :inline t
    :enabled t
    :guard-hints (("goal" :in-theory (enable snode->regp)))
    (mbe :logic (snode->regp slot1)
         :exec (logand 1 (the (unsigned-byte 32) slot1))))

  (defcong nat-equiv equal (snode->regp slot) 1
    :hints(("Goal" :in-theory (enable snode->regp))))

  (defthm bitp-snode->regp
    (bitp (snode->regp slot1))
    :hints(("Goal" :in-theory (enable snode->regp))))

  (definlined snode->fanin (slot)
    (declare (type (integer 0 *) slot))
    (mbe :logic (ash (lnfix slot) -2)
         :exec (if (<= slot #xffffffff)
                   (ash (the (unsigned-byte 32) slot) -2)
                 (ash (lnfix slot) -2))))

  (define snode->fanin^ ((slot :type (unsigned-byte 32)))
    :inline t
    :enabled t
    :guard-hints (("goal" :in-theory (enable snode->fanin)))
    (mbe :logic (snode->fanin slot)
         :exec (the (unsigned-byte 30) (ash (the (unsigned-byte 32) slot) -2))))

  (defcong nat-equiv equal (snode->fanin slot) 1
    :hints(("Goal" :in-theory (enable snode->fanin))))

  (definlined snode->ionum (slot1)
    (declare (type (integer 0 *) slot1))
    (mbe :logic (ash (lnfix slot1) -2)
         :exec (if (<= slot1 #xffffffff)
                   (ash (the (unsigned-byte 32) slot1) -2)
                 (ash (lnfix slot1) -2))))

  (define snode->ionum^ ((slot1 :type (unsigned-byte 32)))
    :inline t
    :enabled t
    :guard-hints (("goal" :in-theory (enable snode->ionum)))
    (mbe :logic (snode->ionum slot1)
         :exec (the (unsigned-byte 30) (ash (the (unsigned-byte 32) slot1) -2))))

  (defcong nat-equiv equal (snode->ionum slot) 1
    :hints(("Goal" :in-theory (enable snode->ionum))))

  ;; Reg implementation:
  ;; RO -> RI (slot 0, 0 when unconnected)
  ;; RO -> regnum (slot 1)
  ;; RI -> regnum (slot 1, 0 when unconnected)
  ;; regnum -> RO normally, RI when RI unconnected

  ;; Const-time lookups in all directions:
  ;; unconnected RO:   RO <-> regnum
  ;; unconnected RI:   RO <-> regnum
  ;; connected RO/RI:   RO --> RI --> regnum
  ;;                     \______________/

  ;; (definlined snode->regid (slot0)
  ;;   (declare (type (integer 0 *) slot0))
  ;;   (mbe :logic (ash (lnfix slot0) -2)
  ;;        :exec (if (<= slot0 #xffffffff)
  ;;                  (ash (the (unsigned-byte 32) slot0) -2)
  ;;                (ash (lnfix slot0) -2))))

  ;; (define snode->regid^ ((slot0 :type (unsigned-byte 32)))
  ;;   :inline t
  ;;   :enabled t
  ;;   :guard-hints (("goal" :in-theory (enable snode->regid)))
  ;;   (mbe :logic (snode->regid slot0)
  ;;        :exec (the (unsigned-byte 30) (ash (the (unsigned-byte 32) slot0) -2))))

  ;; (defthm natp-of-snode->regid
  ;;   (natp (snode->regid slot0))
  ;;   :rule-classes :type-prescription)

  ;; (defcong nat-equiv equal (snode->regid slot) 1
  ;;   :hints(("Goal" :in-theory (enable snode->regid))))
  )


(defsection mk-snode

  (definlined mk-snode (type regp phase fanin0 fanin1)
    (declare (type (integer 0 *) fanin0)
             (type (integer 0 *) fanin1)
             (type (integer 0 3) type)
             (type bit regp)
             (type bit phase))
    (mbe :logic (mv (logior (ash (lnfix fanin0) 2)
                            (logand 3 type))
                    (logior (acl2::lbfix regp)
                            (ash (acl2::lbfix phase) 1)
                            (ash (lnfix fanin1) 2)))
         :exec (if (and (<= fanin0 #x3fffffff)
                        (<= fanin1 #x3fffffff))
                   (mv (logior (the (unsigned-byte 32) (ash (the (unsigned-byte 30) fanin0) 2))
                               (the (unsigned-byte 2) type))
                       (logior (the bit regp)
                               (the (unsigned-byte 2) (ash (the bit phase) 1))
                               (the (unsigned-byte 32) (ash (the (unsigned-byte 30) fanin1) 2))))
                 (mv (logior (ash (lnfix fanin0) 2)
                             type)
                     (logior (the bit regp)
                             (the (unsigned-byte 2) (ash (the bit phase) 1))
                             (ash (lnfix fanin1) 2))))))

  (define mk-snode^ ((type (unsigned-byte-p 2 type) :type (unsigned-byte 2))
                     (regp bitp :type bit)
                     (phase bitp :type bit)
                     (fanin0 (unsigned-byte-p 30 fanin0) :type (unsigned-byte 30))
                     (fanin1 (unsigned-byte-p 30 fanin1) :type (unsigned-byte 30)))
    :inline t
    :enabled t
    :split-types t
    :guard-hints (("goal" :in-theory (enable mk-snode)))
    (mbe :logic (mk-snode type regp phase fanin0 fanin1)
         :exec (mv (the (unsigned-byte 32)
                        (logior (the (unsigned-byte 32) (ash (the (unsigned-byte 30) fanin0) 2))
                                (the (unsigned-byte 2) type)))
                   (the (unsigned-byte 32)
                        (logior (the bit regp)
                                (the (unsigned-byte 2) (ash (the bit phase) 1))
                                (the (unsigned-byte 32) (ash (the (unsigned-byte 30) fanin1) 2)))))))

  (defmvtypes aignet::mk-snode$inline (natp natp))

  (local (in-theory (enable mk-snode)))

  (defthm snode->type-of-mk-snode
    (equal (snode->type (mv-nth 0 (mk-snode type regp phase fanin0 fanin1)))
           (logand 3 type))
    :hints(("Goal" :in-theory (enable snode->type))))

  (defthm snode->regp-of-mk-snode
    (equal (snode->regp (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
           (bfix regp))
    :hints(("Goal" :in-theory (e/d (snode->regp
                                    bitops::loghead-of-ash)))))

  (defthm snode->phase-of-mk-snode
    (equal (snode->phase (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
           (bfix phase))
    :hints(("Goal" :in-theory (e/d (snode->phase
                                    bitops::loghead-of-ash)))))

  (defthm snode->fanin-of-mk-snode
    (and (equal (snode->fanin (mv-nth 0 (mk-snode type regp phase fanin0 fanin1)))
                (nfix fanin0))
         (equal (snode->fanin (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
                (nfix fanin1)))
    :hints(("Goal" :in-theory (enable snode->fanin))))

  ;; (defthm snode->regid-of-mk-snode-0
  ;;   (equal (snode->regid (mv-nth 0 (mk-snode type regp phase fanin0 fanin1)))
  ;;          (nfix fanin0))
  ;;   :hints(("Goal" :in-theory (enable snode->regid))))

  ;; (defthm snode->regid-of-mk-snode-1
  ;;   (equal (snode->regid (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
  ;;          (nfix fanin1))
  ;;   :hints(("Goal" :in-theory (enable snode->regid))))


  (defthm snode->ionum-of-mk-snode
    (equal (snode->ionum (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
           (nfix fanin1))
    :hints(("Goal" :in-theory (enable snode->ionum))))

  (defthm normalize-mk-snode-0
    (implies (syntaxp (not (and (equal regp ''0)
                                (equal phase ''0)
                                (equal fanin1 ''0))))
             (equal (mv-nth 0 (mk-snode type regp phase fanin0 fanin1))
                    (mv-nth 0 (mk-snode type 0 0 fanin0 0)))))

  (defthm normalize-mk-snode-1
    (implies (syntaxp (not (and (equal fanin0 ''0)
                                (equal type ''0))))
             (equal (mv-nth 1 (mk-snode type regp phase fanin0 fanin1))
                    (mv-nth 1 (mk-snode 0 regp phase 0 fanin1)))))

  (defthm unsigned-byte-p-of-mk-snode-0
    (and (implies (unsigned-byte-p 30 fanin0)
                  (unsigned-byte-p 32 (mv-nth 0 (mk-snode type regp phase fanin0 fanin1))))
         (implies (unsigned-byte-p 30 fanin1)
                  (unsigned-byte-p 32 (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))))))

