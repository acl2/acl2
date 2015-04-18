

(in-package "AIGNET")


(include-book "litp")
(include-book "std/util/defmvtypes" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
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
    (logand 3 (lnfix slot0)))

  (defthm snode->type-natp
    (natp (snode->type slot0))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (snode->type slot) 1
    :hints(("Goal" :in-theory (enable snode->type))))

  (defthm snode->type-bound
    (< (snode->type slot0) 4)
    :hints(("Goal" :in-theory (enable snode->type)
            :expand ((:free (m) (acl2::loghead 2 m))
                     (:free (m) (acl2::loghead 1 m))
                     (:free (m) (acl2::loghead 0 m)))))
    :rule-classes :linear)

  (definlined snode->phase (slot1)
    (declare (type (integer 0 *) slot1))
    (logand 1 (ash (lnfix slot1) -1)))

  (defcong nat-equiv equal (snode->phase slot) 1
    :hints(("Goal" :in-theory (enable snode->phase))))

  (defthm bitp-snode->phase
    (bitp (snode->phase slot1))
    :hints(("Goal" :in-theory (enable snode->phase))))

  (definlined snode->regp (slot1)
    (declare (type (integer 0 *) slot1))
    (logand 1 (lnfix slot1)))

  (defcong nat-equiv equal (snode->regp slot) 1
    :hints(("Goal" :in-theory (enable snode->regp))))

  (defthm bitp-snode->regp
    (bitp (snode->regp slot1))
    :hints(("Goal" :in-theory (enable snode->regp))))

  (definlined snode->fanin (slot)
    (declare (type (integer 0 *) slot))
    (to-lit (ash (lnfix slot) -2)))

  (defcong nat-equiv equal (snode->fanin slot) 1
    :hints(("Goal" :in-theory (enable snode->fanin))))

  (definlined snode->ionum (slot1)
    (declare (type (integer 0 *) slot1))
    (ash (lnfix slot1) -2))

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

  (definlined snode->regid (slot0)
    (declare (type (integer 0 *) slot0))
    (ash (lnfix slot0) -2))

  (defthm natp-of-snode->regid
    (natp (snode->regid slot0))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (snode->regid slot) 1
    :hints(("Goal" :in-theory (enable snode->regid)))))


(defsection mk-snode

  (definlined mk-snode (type regp phase fanin0 fanin1)
    (declare (type (integer 0 *) fanin0)
             (type (integer 0 *) fanin1)
             (type (integer 0 3) type)
             (type bit regp)
             (type bit phase))
    (mv (logior (ash (lnfix fanin0) 2)
                (logand 3 type))
        (logior (acl2::lbfix regp)
                (ash (acl2::lbfix phase) 1)
                (ash (lnfix fanin1) 2))))

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
                (to-lit fanin0))
         (equal (snode->fanin (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
                (to-lit fanin1)))
    :hints(("Goal" :in-theory (enable snode->fanin))))

  (defthm snode->regid-of-mk-snode-0
    (equal (snode->regid (mv-nth 0 (mk-snode type regp phase fanin0 fanin1)))
           (nfix fanin0))
    :hints(("Goal" :in-theory (enable snode->regid))))

  (defthm snode->regid-of-mk-snode-1
    (equal (snode->regid (mv-nth 1 (mk-snode type regp phase fanin0 fanin1)))
           (nfix fanin1))
    :hints(("Goal" :in-theory (enable snode->regid))))

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
                    (mv-nth 1 (mk-snode 0 regp phase 0 fanin1))))))
  
