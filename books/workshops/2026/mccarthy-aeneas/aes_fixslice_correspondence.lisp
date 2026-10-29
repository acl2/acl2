;; Phase 2 of the fixslice-AES experiment: the state <-> fixslice correspondence.
;;
;; The bijection book proved inv_bitslice . bitslice = id for the concrete
;; 32-byte-variable form (what GL bit-blasts). Here we (a) lift it to a general
;; 16-byte-LIST form Phase 3 can reuse, and (b) connect the fixslice packing to
;; Kestrel's AES state representation `statep` (copyarraytostate), defining the
;; correspondence map that Phase 3's per-op equivalences will be stated over.
;;
;; Loaded through the GL-compatible variant (aes_fixslice_bijection pulls in the
;; -gl functions, GL, and the certified 32-var bijection theorem); Kestrel's
;; aes-spec adds `statep`/`copyarraytostate`/`inp` in package AES.
(in-package "ACL2")
(include-book "aes_fixslice_bijection")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)

;; ---------------------------------------------------------------------------
;; A length-16 true-list equals the explicit list of its 16 elements -- rewrites
;; a general block into the shape the 32-variable GL theorem matches. Forcing
;; consp at each of the 16 levels lets car/cdr-elim + nth opening close it.
(defthmd expand-len-16
  (implies (and (true-listp x) (equal (len x) 16))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x) (nth 9 x) (nth 10 x) (nth 11 x) (nth 12 x) (nth 13 x) (nth 14 x) (nth 15 x)) x))
  :hints (("Goal" :in-theory (enable nth)
           :expand ((len x)
                    (len (cdr x))
                    (len (cdr (cdr x)))
                    (len (cdr (cdr (cdr x))))
                    (len (cdr (cdr (cdr (cdr x)))))
                    (len (cdr (cdr (cdr (cdr (cdr x))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))))))))))

;; Kestrel's `inp` (a 16-byte block) unpacked into the facts the bridge needs.
(defthm true-listp-when-inp
  (implies (aes::inp x) (true-listp x))
  :hints (("Goal" :in-theory (enable aes::inp acl2::bv-arrayp))))

(defthm len-when-inp
  (implies (aes::inp x) (equal (len x) 16))
  :hints (("Goal" :in-theory (enable aes::inp acl2::bv-arrayp))))

(defthm unsigned-byte-p-8-of-nth-when-inp
  (implies (and (aes::inp x) (natp i) (< i 16))
           (unsigned-byte-p 8 (nth i x)))
  :hints (("Goal" :in-theory (enable aes::inp acl2::bv-arrayp))))

;; ---------------------------------------------------------------------------
;; General-form bijection: the reusable crux lemma. For any two 16-byte blocks,
;; unbitslicing a freshly bitsliced pair returns exactly those blocks. Proved by
;; instantiating the 32-var GL theorem at the blocks' elements, then folding the
;; explicit element-lists back to the blocks with expand-len-16. bitslice /
;; inv_bitslice / inp are kept closed so nothing expands the huge definitions.
(defthm inv-bitslice-of-bitslice-general
  (implies (and (aes::inp blk0) (aes::inp blk1))
           (equal (aes-fixslice-encrypt-inv-bitslice
                    (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)))
                  (ok (list blk0 blk1))))
  :hints (("Goal"
           ;; Keep the big functions + inp closed; disable the result-ok
           ;; splitter and nth-opening so the GL instance matches the goal
           ;; directly after expand-len-16 folds the element-lists back.
           :in-theory (e/d (expand-len-16)
                           (inv-bitslice-of-bitslice-is-identity
                            aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice
                            aes::inp equal-of-result-ok nth))
           :use (:instance inv-bitslice-of-bitslice-is-identity
                  (a0 (nth 0 blk0))
                  (a1 (nth 1 blk0))
                  (a2 (nth 2 blk0))
                  (a3 (nth 3 blk0))
                  (a4 (nth 4 blk0))
                  (a5 (nth 5 blk0))
                  (a6 (nth 6 blk0))
                  (a7 (nth 7 blk0))
                  (a8 (nth 8 blk0))
                  (a9 (nth 9 blk0))
                  (a10 (nth 10 blk0))
                  (a11 (nth 11 blk0))
                  (a12 (nth 12 blk0))
                  (a13 (nth 13 blk0))
                  (a14 (nth 14 blk0))
                  (a15 (nth 15 blk0))
                  (b0 (nth 0 blk1))
                  (b1 (nth 1 blk1))
                  (b2 (nth 2 blk1))
                  (b3 (nth 3 blk1))
                  (b4 (nth 4 blk1))
                  (b5 (nth 5 blk1))
                  (b6 (nth 6 blk1))
                  (b7 (nth 7 blk1))
                  (b8 (nth 8 blk1))
                  (b9 (nth 9 blk1))
                  (b10 (nth 10 blk1))
                  (b11 (nth 11 blk1))
                  (b12 (nth 12 blk1))
                  (b13 (nth 13 blk1))
                  (b14 (nth 14 blk1))
                  (b15 (nth 15 blk1))))))

;; ---------------------------------------------------------------------------
;; The correspondence map phi. A fixslice State batches two blocks; project one
;; lane back to its 16 bytes (via inv_bitslice) and load it into Kestrel's 4x4
;; state exactly as Kestrel's own `cipher` entry does (copyarraytostate).
(defund fixslice->block (st lane)
  (nth lane (result-ok->val (aes-fixslice-encrypt-inv-bitslice st))))

(defund fixslice->statep (st lane)
  (aes::copyarraytostate (fixslice->block st lane)))

;; Entry-point correspondence: bitslicing a raw block and mapping it back
;; through phi yields exactly Kestrel's state for that block. This is the
;; representation bridge Phase 3's per-op lemmas will be stated across.
(defthm fixslice->statep-of-bitslice
  (implies (and (aes::inp blk0) (aes::inp blk1))
           (and (equal (fixslice->statep
                         (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)) 0)
                       (aes::copyarraytostate blk0))
                (equal (fixslice->statep
                         (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)) 1)
                       (aes::copyarraytostate blk1))))
  ;; Keep bitslice/inv_bitslice closed so the general-bijection rewrite fires
  ;; instead of ACL2 opening the huge definitions.
  :hints (("Goal" :in-theory (e/d (fixslice->statep fixslice->block)
                                  (aes-fixslice-encrypt-bitslice
                                   aes-fixslice-encrypt-inv-bitslice
                                   inv-bitslice-of-bitslice-is-identity)))))

;; ...and the mapped state is a well-formed Kestrel statep (4x4 bytes).
(defthm statep-of-fixslice->statep-of-bitslice
  (implies (and (aes::inp blk0) (aes::inp blk1))
           (and (aes::statep (fixslice->statep
                               (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)) 0))
                (aes::statep (fixslice->statep
                               (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)) 1))))
  ;; Rewrite phi(bitslice ..) to copyarraytostate via the lemma above (so keep
  ;; fixslice->statep and the big functions closed), then statep follows.
  :hints (("Goal" :in-theory (e/d (aes::statep-of-copyarraytostate)
                                  (aes-fixslice-encrypt-bitslice
                                   aes-fixslice-encrypt-inv-bitslice
                                   inv-bitslice-of-bitslice-is-identity)))))
