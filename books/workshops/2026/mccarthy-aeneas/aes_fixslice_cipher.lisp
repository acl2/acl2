; Phase 5 -- CIPHER SIDE, part 1: the extracted aes128_encrypt collapses onto
; a clean value-chain model.
;
; The extracted body is bitslice ; ark@0 ; 9x[sub_bytes ; mix_columns_c ;
; ark@8r] ; shift_rows_2 ; sub_bytes ; ark@80 ; inv_bitslice -- 33 ops,
; single-threaded.  As with the key schedule: (1) length-only :ok facts let
; every ok-binder collapse from array bounds alone; (2) enc-model is the same
; chain as a pure val-composition; (3) enc-collapse equates them.  The round
; keys enter only through add_round_key's window reads, captured by arkw
; (word-wise xor against rd8), so the schedule windows plug in directly.
(in-package "ACL2")
(include-book "aes_fixslice_keyread")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ===========================================================================
;; (C1) add_round_key: loop spec (word-wise xor against the rkeys window;
;; the extracted loop is upstream's iter_mut().zip() -- see ark-form-n).
(defund arkw (s w)
  (list (u32-xor (nth 0 s) (nth 0 w)) (u32-xor (nth 1 s) (nth 1 w))
        (u32-xor (nth 2 s) (nth 2 w)) (u32-xor (nth 3 s) (nth 3 w))
        (u32-xor (nth 4 s) (nth 4 w)) (u32-xor (nth 5 s) (nth 5 w))
        (u32-xor (nth 6 s) (nth 6 w)) (u32-xor (nth 7 s) (nth 7 w))))

;; the loop spec as a generic accumulator; the 8-step instance is arkw.
(defun arkw-spec (i e s rk off)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (arkw-spec (+ i 1) e (update-nth i (u32-xor (nth i s) (nth (+ off i) rk)) s) rk off)
    s))
;; ===========================================================================
;; (C2) length-only :ok / len / true-listp for the remaining cipher ops.
;; All by the explicit-8 template: prove on an explicit 8-list (everything
;; computes; no shape splits), lift via expand-len-8.

;; ror wraps u32-rotate-right, whose body is (ok <arith>): :ok unconditionally.
;; Proved under ground-zero so the mod/logior/ash arithmetic never opens.
(local (defthm rk-of-ror
  (equal (result-kind (aes-fixslice-encrypt-ror x y)) :ok)
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
             '((:definition aes-fixslice-encrypt-ror)
               (:definition u32-rotate-right)
               (:rewrite rk-of-ok2)))))))

(local (defthm rk-mc0-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm len-mc0-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm tl-mc0-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(defthm result-kind-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance rk-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance len-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-0 nth)
           :use ((:instance tl-mc0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc1-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm len-mc1-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm tl-mc1-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(defthm result-kind-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance rk-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance len-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-1 nth)
           :use ((:instance tl-mc1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc2-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm len-mc2-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm tl-mc2-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(defthm result-kind-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance rk-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance len-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-2 nth)
           :use ((:instance tl-mc2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-mc3-explicit
  (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm len-mc3-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(local (defthm tl-mc3-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))
(defthm result-kind-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance rk-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm len-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance len-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm true-listp-of-mc3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-mix-columns-3 nth)
           :use ((:instance tl-mc3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

;; inv_bitslice plumbing: delta_swap_2 / shr / u8-cast are :ok for the
;; constant shifts and 255-masks that appear, so the ops stay opaque.
(local (defthm rk-of-ds2
  (implies (< (nfix shift) 32)
           (equal (result-kind (aes-fixslice-encrypt-delta-swap-2 a b shift mask)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-2)))))
(local (defthm rk-of-u32-shr-lt
  (implies (< (nfix n) 32)
           (equal (result-kind (u32-shr x n)) :ok))))
(local (defthm rk-invb-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-bitslice (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-bitslice)
                                  (u32-xor u32-and u32-or u32-shl u32-shr
                                   aes-fixslice-encrypt-delta-swap-2
                                   vec-index-range vec-update-range
                                   slice-copy-from-slice u32-to-le-bytes
                                   take nthcdr append update-nth))))))
(local (defthm rp-invb-explicit
  (result-p (aes-fixslice-encrypt-inv-bitslice (list a0 a1 a2 a3 a4 a5 a6 a7)))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-bitslice)
                                  (u32-xor u32-and u32-or u32-shl u32-shr
                                   aes-fixslice-encrypt-delta-swap-2
                                   vec-index-range vec-update-range
                                   slice-copy-from-slice u32-to-le-bytes
                                   take nthcdr append update-nth))))))
(defthm result-kind-of-inv-bitslice-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-bitslice s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-bitslice nth)
           :use ((:instance rk-invb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
(defthm result-p-of-inv-bitslice
  (implies (and (true-listp s) (equal (len s) 8))
           (result-p (aes-fixslice-encrypt-inv-bitslice s)))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-bitslice nth)
           :use ((:instance rp-invb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
;; sub_bytes true-listp (rk/len already in keydecomp).
(local (defthm tl-sb-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(defthm true-listp-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance tl-sb-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
;; shift_rows_2 direct forms (the isr2 lemmas are about the alias fn).
(defthm result-kind-of-sr2-100
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :use result-kind-of-isr2-len
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm len-of-sr2-100-d
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))) 8))
  :hints (("Goal" :use len-of-isr2-len
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm true-listp-of-sr2-100-d
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
  :hints (("Goal" :use true-listp-of-isr2-100
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2) (aes-fixslice-encrypt-shift-rows-2)))))

;; add_round_key value/shape at fuel 100 via the loop spec.
(defthm len-of-arkw-spec
  (implies (and (natp i) (natp e) (<= e (len s)))
           (equal (len (arkw-spec i e s rk off)) (len s)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth)))))
(defthm true-listp-of-arkw-spec
  (implies (true-listp s) (true-listp (arkw-spec i e s rk off)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth)))))
;; upstream signature (state, rkey-window): the massert demands the window
;; length exactly; generic fuel (the round loop calls at 99/98/97).  The
;; extracted loop is the upstream iter_mut().zip() form (roadmap #8): next
;; reads BOTH original lists (writes are pending in the defunctionalized
;; back list; the &mut side's cursor drives them home afterwards), so at
;; window length 8 the loop unrolls completely by rewriting -- the
;; (:free ...) :expand hint re-fires at every exposed fuel, (< 8 (nfix n))
;; deciding the zp tests -- and the update-nth nest meets arkw-spec's under
;; the std/lists commuting rules.
(defthm ark-form-n
  (implies (and (equal (len w) 8) (<= 8 (len s)) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key n s w)
                  (ok (arkw-spec 0 8 s w 0))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-add-round-key-loop0 n it bk))
                    (:free (i s) (arkw-spec i 8 s w 0)))
           :in-theory (e/d (aes-fixslice-encrypt-add-round-key zp nfix)
                           (u32-xor)))))
(defthm ark-form100
  (implies (and (equal (len w) 8) (<= 8 (len s)))
           (equal (aes-fixslice-encrypt-add-round-key 100 s w)
                  (ok (arkw-spec 0 8 s w 0))))
  :hints (("Goal" :use (:instance ark-form-n (n 100))
           :in-theory (disable aes-fixslice-encrypt-add-round-key arkw-spec))))

;; ===========================================================================
;; (C3) enc-model: the encrypt body (prelude ; the restored upstream round
;; LOOP ; finale) collapses onto a pure value chain.
;; enc-chain rounds: ark0 | 9 x [sub_bytes ; mix_columns_c ; ark(8r)] with
;; c = r mod 4 | shift_rows_2 ; sub_bytes ; ark80.  inv_bitslice stays outside.
;; The loop contributes the nine middle rounds via enc-loop-collapse below.
;; A single shape predicate.  The C2 rules carry (true-listp s) AND
;; (equal (len s) 8) as separate hyps; relieving both at chain depth k
;; re-descends the whole nest per hyp -- a 2^k relief tree (measured: ~x5
;; per layer).  One predicate with one closure rule per op makes each
;; descent linear, so the 33-op collapse is O(k^2) overall.
(defund st8p (s) (and (true-listp s) (equal (len s) 8)))
(local (defthm st8p-open
  (implies (st8p s) (and (true-listp s) (equal (len s) 8)))
  :hints (("Goal" :in-theory (enable st8p)))))
(defthm st8p-of-bitslice
  (implies (and (aes::inp b0) (aes::inp b1))
           (st8p (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
  :hints (("Goal" :in-theory (e/d (st8p len-when-wstatep true-listp-when-wstatep)
                                  (aes-fixslice-encrypt-bitslice))
           :use (:instance wstatep-of-bitslice))))
(defthm st8p-of-arkw-spec
  (implies (st8p s) (st8p (arkw-spec 0 8 s rk off)))
  :hints (("Goal" :in-theory (e/d (st8p) (arkw-spec u32-xor nth)))))
(defthm st8p-of-sb
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-sub-bytes)))))
(defthm rk-of-sb-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-sub-bytes)))))
(defthm st8p-of-mc0
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-0)))))
(defthm rk-of-mc0-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-0)))))
(defthm st8p-of-mc1
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-1)))))
(defthm rk-of-mc1-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-1)))))
(defthm st8p-of-mc2
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-2)))))
(defthm rk-of-mc2-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-2)))))
(defthm st8p-of-mc3
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-3)))))
(defthm rk-of-mc3-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-mix-columns-3)))))
(defthm st8p-of-sr2
  (implies (st8p s) (st8p (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm rk-of-sr2-st
  (implies (st8p s) (equal (result-kind (aes-fixslice-encrypt-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-shift-rows-2)))))
(defthm ark-form-n-st
  (implies (and (st8p s) (equal (len w) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key n s w)
                  (ok (arkw-spec 0 8 s w 0))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-add-round-key arkw-spec))
           :use ark-form-n)))
;; ---- the round-key windows: each synthesized Index<RangeX> read is rd8 ----
(local (defthm nthcdr-0-id (implies (true-listp rk) (equal (nthcdr 0 rk) rk))))
(defthm take8-nthcdr-is-rd8
  (implies (and (natp off) (<= (+ off 8) (len rk)) (true-listp rk))
           (equal (take 8 (nthcdr off rk)) (rd8 rk off)))
  :hints ((acl2::equal-by-nths-hint)
          '(:in-theory (e/d (rd8) (nth take nthcdr)))))
(local (defthm arkw-window-shift-c   ; arkw-spec over the rd8 window = at off
  (implies (and (natp i) (natp e) (<= e 8) (natp off))
           (equal (arkw-spec i e s (rd8 rk off) 0)
                  (arkw-spec i e s rk off)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth rd8))))
  :rule-classes nil))
(defthm rk-of-window-to
  (implies (<= 8 (len rk))
           (equal (result-kind (core-array-impl-core-ops-index-index-core-ops-range-rangeto-usize-for-u32-88usize-index-u32-core-ops-range-rangeto-usize-88usize- rk (core-ops-range-rangeto-usize- 8))) :ok))
  :hints (("Goal" :in-theory (enable core-array-impl-core-ops-index-index-core-ops-range-rangeto-usize-for-u32-88usize-index-u32-core-ops-range-rangeto-usize-88usize-))))
(defthm ark-of-window-to
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key n s
                    (result-ok->val (core-array-impl-core-ops-index-index-core-ops-range-rangeto-usize-for-u32-88usize-index-u32-core-ops-range-rangeto-usize-88usize- rk (core-ops-range-rangeto-usize- 8))))
                  (ok (arkw-spec 0 8 s rk 0))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (core-array-impl-core-ops-index-index-core-ops-range-rangeto-usize-for-u32-88usize-index-u32-core-ops-range-rangeto-usize-88usize-) (aes-fixslice-encrypt-add-round-key arkw-spec rd8 nth))
           :use ((:instance take8-nthcdr-is-rd8 (off 0))
                 (:instance ark-form-n (w (rd8 rk 0)))
                 (:instance arkw-window-shift-c (i 0) (e 8) (off 0))))))
(defthm rk-of-window-from80
  (implies (equal (len rk) 88)
           (equal (result-kind (core-array-impl-core-ops-index-index-core-ops-range-rangefrom-usize-for-u32-88usize-index-u32-core-ops-range-rangefrom-usize-88usize- rk (core-ops-range-rangefrom-usize- 80))) :ok))
  :hints (("Goal" :in-theory (enable core-array-impl-core-ops-index-index-core-ops-range-rangefrom-usize-for-u32-88usize-index-u32-core-ops-range-rangefrom-usize-88usize-))))
(defthm ark-of-window-from80
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key n s
                    (result-ok->val (core-array-impl-core-ops-index-index-core-ops-range-rangefrom-usize-for-u32-88usize-index-u32-core-ops-range-rangefrom-usize-88usize- rk (core-ops-range-rangefrom-usize- 80))))
                  (ok (arkw-spec 0 8 s rk 80))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (core-array-impl-core-ops-index-index-core-ops-range-rangefrom-usize-for-u32-88usize-index-u32-core-ops-range-rangefrom-usize-88usize-) (aes-fixslice-encrypt-add-round-key arkw-spec rd8 nth))
           :use ((:instance take8-nthcdr-is-rd8 (off 80))
                 (:instance ark-form-n (w (rd8 rk 80)))
                 (:instance arkw-window-shift-c (i 0) (e 8) (off 80))))))
(defthm rk-of-window-range
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len rk)))
           (equal (result-kind (core-array-impl-core-ops-index-index-core-ops-range-range-usize-for-u32-88usize-index-u32-core-ops-range-range-usize-88usize- rk (core-ops-range-range-usize- lo hi))) :ok))
  :hints (("Goal" :in-theory (enable core-array-impl-core-ops-index-index-core-ops-range-range-usize-for-u32-88usize-index-u32-core-ops-range-range-usize-88usize-))))
(defthm ark-of-window-range
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88)
                (natp lo) (<= (+ lo 8) 88) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-add-round-key n s
                    (result-ok->val (core-array-impl-core-ops-index-index-core-ops-range-range-usize-for-u32-88usize-index-u32-core-ops-range-range-usize-88usize- rk (core-ops-range-range-usize- lo (+ lo 8)))))
                  (ok (arkw-spec 0 8 s rk lo))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (core-array-impl-core-ops-index-index-core-ops-range-range-usize-for-u32-88usize-index-u32-core-ops-range-range-usize-88usize-) (aes-fixslice-encrypt-add-round-key arkw-spec rd8 nth))
           :use ((:instance take8-nthcdr-is-rd8 (off lo))
                 (:instance ark-form-n (w (rd8 rk lo)))
                 (:instance arkw-window-shift-c (i 0) (e 8) (off lo))))))

(defund enc-chain (rk s)
  (b* ((s (arkw-spec 0 8 s rk 0))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 8))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 16))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 24))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 32))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 40))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 48))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 56))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 64))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 72))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-sub-bytes (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s)))) rk 80)))
    s))

;; the restored upstream round loop (bare loop{...break}, counter rk_off) at
;; fuel 100 IS the nine middle rounds: three explicit expansions of the loop
;; body (fuel 100 at rk_off 8, 99 at 40, 98 at 72 -- the break fires after the
;; first quarter of the third body), each quarter's add_round_key collapsed by
;; the generic-fuel ark-form-n-st.  Same pinned-theory discipline as
;; enc-collapse below: the b* ok-binder nest otherwise explodes in preprocessing.
(defthm enc-loop-collapse
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88))
           (equal (aes-fixslice-encrypt-aes128-encrypt-loop0 100 rk s 8)
                  (ok (b* (
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 8))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 16))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 24))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 32))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 40))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 48))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 56))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 64))
       (s (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-sub-bytes s)))) rk 72)))
                        s))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (sv) (aes-fixslice-encrypt-aes128-encrypt-loop0 100 rk sv 8))
                    (:free (sv) (aes-fixslice-encrypt-aes128-encrypt-loop0 99 rk sv 40))
                    (:free (sv) (aes-fixslice-encrypt-aes128-encrypt-loop0 98 rk sv 72)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite st8p-of-arkw-spec) (:rewrite st8p-of-sb)
                          (:rewrite st8p-of-mc0) (:rewrite st8p-of-mc1)
                          (:rewrite st8p-of-mc2) (:rewrite st8p-of-mc3)
                          (:rewrite rk-of-sb-st)
                          (:rewrite rk-of-mc0-st) (:rewrite rk-of-mc1-st)
                          (:rewrite rk-of-mc2-st) (:rewrite rk-of-mc3-st)
                          (:rewrite ark-of-window-range) (:rewrite rk-of-window-range)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart usize-add)
                          (:executable-counterpart result-kind$inline)
                          (:executable-counterpart result-ok->val$inline)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm enc-collapse
  (implies (and (aes::inp b0) (aes::inp b1)
                (true-listp rk) (equal (len rk) 88))
           (equal (aes-fixslice-encrypt-aes128-encrypt 100 rk b0 b1)
                  (aes-fixslice-encrypt-inv-bitslice
                    (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-encrypt)
                          (:definition enc-chain)
                          (:definition not)
                          (:rewrite bitslice-ok) (:rewrite st8p-of-bitslice)
                          (:executable-counterpart array-repeat)
                          (:rewrite st8p-of-arkw-spec) (:rewrite st8p-of-sb)
                          (:rewrite st8p-of-mc0) (:rewrite st8p-of-mc1)
                          (:rewrite st8p-of-mc2) (:rewrite st8p-of-mc3)
                          (:rewrite st8p-of-sr2)
                          (:rewrite rk-of-sb-st)
                          (:rewrite rk-of-mc0-st) (:rewrite rk-of-mc1-st)
                          (:rewrite rk-of-mc2-st) (:rewrite rk-of-mc3-st)
                          (:rewrite rk-of-sr2-st)
                          (:rewrite ark-of-window-to) (:rewrite rk-of-window-to)
                          (:rewrite ark-of-window-from80) (:rewrite rk-of-window-from80)
                          (:rewrite enc-loop-collapse)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm st8p-of-enc-chain
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88))
           (st8p (enc-chain rk s)))
  :hints (("Goal" :in-theory (e/d (enc-chain)
                    (arkw-spec u32-xor nth st8p
                     aes-fixslice-encrypt-sub-bytes
                     aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1
                     aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3
                     aes-fixslice-encrypt-shift-rows-2)))))
(defthm result-kind-of-encrypt
  (implies (and (aes::inp b0) (aes::inp b1) (true-listp rk) (equal (len rk) 88))
           (equal (result-kind (aes-fixslice-encrypt-aes128-encrypt 100 rk b0 b1)) :ok))
  :hints (("Goal" :in-theory (e/d () (aes-fixslice-encrypt-aes128-encrypt
                                      aes-fixslice-encrypt-inv-bitslice enc-chain
                                      aes-fixslice-encrypt-bitslice st8p))
           :use (enc-collapse
                 (:instance st8p-of-enc-chain (s (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
                 (:instance st8p-open (s (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))))
                 (:instance result-kind-of-inv-bitslice-len
                   (s (enc-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))))))))
