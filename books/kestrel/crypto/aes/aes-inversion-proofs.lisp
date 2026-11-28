; AES Inversion Proofs
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AES")

(include-book "aes-spec")

;; Theorems AES-128-PERMUTATION-OF-BLOCKS, AES-192-PERMUTATION-OF-BLOCKS,
;; and AES-256-PERMUTATION-OF-BLOCKS collect the block-level results.
;; EQINVCIPHER-IS-INVCIPHER relates decryption with preprocessed round
;; keys to the original spec.
;;
;; GL proves the S-box lookup identities and scalar laws of the AES byte
;; field.  Matrix multiplication then proves that MixColumn and InvMixColumn
;; are inverses, and matrix linearity proves that InvMixColumn preserves XOR.
;; Induction on the round loops lifts the single-round identities to the cipher.
;; The companion .acl2 file supplies the AES and GL packages at read time.
;; Including the certified book brings in the GL package.  The proof engine
;; itself is a local include used during certification.
;;
;; To rewrite round trips and tests of injectivity at the cipher interface,
;; keep the calls visible to the rewriter.  In the AES package, use
;;
;;   (in-theory (disable cipher invcipher
;;                       aes-128-encrypt aes-128-decrypt
;;                       aes-192-encrypt aes-192-decrypt
;;                       aes-256-encrypt aes-256-decrypt))
;;
;; Block closure also works in the default theory.  GF256MULT-OF-GF256ADD-RIGHT
;; and GF256MULT-OF-GF256ADD-LEFT are disabled expansion rules.  Enabling
;; either makes it available for both GF256ADD and its bytewise BVXOR form.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; S-boxes and scalar arithmetic in the AES byte field

(encapsulate
  ()
  (local (include-book "centaur/gl/gl" :dir :system))

  ;; GL symbolically evaluates the spec and proves coverage of the input
  ;; shape.  The last literal of each initial goal is its conclusion.
  (local
   (defmacro byte-proof (hyp bindings)
     `(gl::gl-hint :hyp ',hyp :concl (car (acl2::last acl2::clause))
                   :g-bindings ,bindings
                   :cov-theory-add '(acl2::bv-arrayp all-unsigned-byte-p))))

  (defthm invsbox-of-sbox
    (implies (bytep x) (equal (nth (nth x (sbox)) (invsbox)) x))
    :hints ((byte-proof (bytep x) (gl::auto-bindings (:nat x 8)))))

  (defthm sbox-of-invsbox
    (implies (bytep x) (equal (nth (nth x (invsbox)) (sbox)) x))
    :hints ((byte-proof (bytep x) (gl::auto-bindings (:nat x 8)))))

  ;; Multiplication in GF(2^8) distributes over bytewise XOR on either side.
  ;; Keep these expansion rules disabled for ordinary cipher rewriting.
  (defthmd gf256mult-of-gf256add-right
    (implies (and (bytep k) (bytep a) (bytep b))
             (equal (gf256mult k (gf256add a b))
                    (gf256add (gf256mult k a) (gf256mult k b))))
    :rule-classes
    (:rewrite
     (:rewrite :corollary
               (implies (and (bytep k) (bytep a) (bytep b))
                        (equal (gf256mult k (bvxor 8 a b))
                               (bvxor 8 (gf256mult k a) (gf256mult k b))))))
    :hints ((byte-proof (and (bytep k) (bytep a) (bytep b))
                        (gl::auto-bindings (:nat k 8) (:nat a 8) (:nat b 8)))))

  (defthmd gf256mult-of-gf256add-left
    (implies (and (bytep k) (bytep a) (bytep b))
             (equal (gf256mult (gf256add a b) k)
                    (gf256add (gf256mult a k) (gf256mult b k))))
    :rule-classes
    (:rewrite
     (:rewrite :corollary
               (implies (and (bytep k) (bytep a) (bytep b))
                        (equal (gf256mult (bvxor 8 a b) k)
                               (bvxor 8 (gf256mult a k) (gf256mult b k))))))
    :hints ((byte-proof (and (bytep k) (bytep a) (bytep b))
                        (gl::auto-bindings (:nat k 8) (:nat a 8) (:nat b 8)))))

  (local
   (defthm gf256mult-associative
     (implies (and (bytep a) (bytep b) (bytep c))
              (equal (gf256mult a (gf256mult b c))
                     (gf256mult (gf256mult a b) c)))
     :hints ((byte-proof (and (bytep a) (bytep b) (bytep c))
                         (gl::auto-bindings (:nat a 8) (:nat b 8) (:nat c 8))))))

  (local
   (defthm gf256mult-by-zero-and-one
     (implies (bytep x)
              (and (equal (gf256mult 0 x) 0)
                   (equal (gf256mult 1 x) x)))
     :hints ((byte-proof (bytep x) (gl::auto-bindings (:nat x 8))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Matrix algebra for MixColumn and InvMixColumn
  ;;
  ;; A word represents a four-byte column vector.  Each matrix is a list
  ;; of four rows.  Its action on a column takes one dot product per row.

  (local (include-book "kestrel/lists-light/nth" :dir :system))
  (local (include-book "kestrel/lists-light/take" :dir :system))
  (local (include-book "kestrel/bv/bvchop" :dir :system))

  (local
   (defthm bytep-of-word-entry
     (implies (and (wordp v) (natp i) (< i 4))
              (bytep (nth i v)))))

  (local
   (defthm wordp-of-matrix-row
     (implies (and (statep m) (natp i) (< i 4))
              (wordp (nth i m)))))

  (local
   (defthm wordp-of-matrix-column
     (implies (and (statep m) (natp i) (< i 4))
              (wordp (acl2::get-column i m)))))

  (local
   (defund dot4 (u v)
     (declare (xargs :guard (and (wordp u) (wordp v))))
     (gf256add (gf256mult (nth 0 u) (nth 0 v))
               (gf256mult (nth 1 u) (nth 1 v))
               (gf256mult (nth 2 u) (nth 2 v))
               (gf256mult (nth 3 u) (nth 3 v)))))

  (local
   (defthm bytep-of-dot4
     (bytep (dot4 u v))
     :hints (("Goal" :in-theory (enable dot4)))))

  (local
   (defund matvec4 (m v)
     (declare (xargs :guard (and (statep m) (wordp v))))
     (list (dot4 (nth 0 m) v) (dot4 (nth 1 m) v)
           (dot4 (nth 2 m) v) (dot4 (nth 3 m) v))))

  (local
   (defthm wordp-of-matvec4
     (wordp (matvec4 m v))
     :hints (("Goal" :in-theory (enable matvec4)))))

  (local
   (defund rowmat4 (u m)
     (declare (xargs :guard (and (wordp u) (statep m))))
     (list (dot4 u (acl2::get-column 0 m)) (dot4 u (acl2::get-column 1 m))
           (dot4 u (acl2::get-column 2 m)) (dot4 u (acl2::get-column 3 m)))))

  (local
   (defthm wordp-of-rowmat4
     (wordp (rowmat4 u m))
     :hints (("Goal" :in-theory (enable rowmat4)))))

  (local
   (defund matmul4 (a b)
     (declare (xargs :guard (and (statep a) (statep b))))
     (list (rowmat4 (nth 0 a) b) (rowmat4 (nth 1 a) b)
           (rowmat4 (nth 2 a) b) (rowmat4 (nth 3 a) b))))

  (local
   (defthm statep-of-matmul4
     (statep (matmul4 a b))
     :hints (("Goal" :in-theory (enable matmul4)))))

  (local (in-theory (enable gf256mult-of-gf256add-right
                            gf256mult-of-gf256add-left)))

  ;; Distributing each coefficient over XOR makes the dot product linear
  ;; in the column.  Applying this identity to each row gives linearity
  ;; of the whole matrix.
  (local
   (defthm dot4-of-wordxor
     (implies (and (wordp u) (wordp a) (wordp b))
              (equal (dot4 u (wordxor a b))
                     (bvxor 8 (dot4 u a) (dot4 u b))))
     :hints (("Goal" :in-theory (enable dot4 wordxor)))))

  (local
   (defthm matvec4-of-wordxor
     (implies (and (statep m) (wordp a) (wordp b))
              (equal (matvec4 m (wordxor a b))
                     (wordxor (matvec4 m a) (matvec4 m b))))
     :hints (("Goal" :expand ((:free (x0 x1 x2 x3 y)
                               (wordxor (list x0 x1 x2 x3) y)))
              :in-theory (enable matvec4)))))

  ;; Reassociating the scalar products in one row gives u . (M v) =
  ;; (u M) . v.  Applying this to each row of A gives A (B v) = (A B) v.
  (local
   (defthm dot4-of-matvec4
     (implies (and (wordp u) (statep m) (wordp v))
              (equal (dot4 u (matvec4 m v))
                     (dot4 (rowmat4 u m) v)))
     :hints (("Goal" :in-theory (enable dot4 matvec4 rowmat4 array-elem-2d)))))

  (local
   (defthm matvec4-of-matvec4
     (implies (and (statep a) (statep b) (wordp v))
              (equal (matvec4 a (matvec4 b v))
                     (matvec4 (matmul4 a b) v)))
     :hints (("Goal" :expand ((matvec4 a (matvec4 b v))
                              (:free (r0 r1 r2 r3) (matvec4 (list r0 r1 r2 r3) v)))
              :in-theory (enable matmul4)))))

  (local (defconst *mix-matrix*
           '((#x02 #x03 #x01 #x01)
             (#x01 #x02 #x03 #x01)
             (#x01 #x01 #x02 #x03)
             (#x03 #x01 #x01 #x02))))
  (local (defconst *invmix-matrix*
           '((#x0e #x0b #x0d #x09)
             (#x09 #x0e #x0b #x0d)
             (#x0d #x09 #x0e #x0b)
             (#x0b #x0d #x09 #x0e))))
  (local (defconst *identity-matrix*
           '((1 0 0 0) (0 1 0 0) (0 0 1 0) (0 0 0 1))))

  (local
   (defthm both-matrix-products-are-identity
     (and (equal (matmul4 *invmix-matrix* *mix-matrix*) *identity-matrix*)
          (equal (matmul4 *mix-matrix* *invmix-matrix*) *identity-matrix*))
     :rule-classes nil))

  (local
   (defthm matvec4-of-identity
     (implies (wordp v) (equal (matvec4 *identity-matrix* v) v))
     :hints (("Goal" :use (:instance acl2::take-does-nothing-simple
                                     (acl2::n 4) (acl2::l v))
              :in-theory (e/d (matvec4 dot4 acl2::take-opener-alt)
                              (acl2::take-does-nothing))))))

  (local
   (defthm mixcolumn-as-matvec4
     (implies (wordp v) (equal (mixcolumn v) (matvec4 *mix-matrix* v)))
     :hints (("Goal" :in-theory (enable mixcolumn matvec4 dot4)))))

  (local
   (defthm invmixcolumn-as-matvec4
     (implies (wordp v) (equal (invmixcolumn v) (matvec4 *invmix-matrix* v)))
     :hints (("Goal" :in-theory (enable invmixcolumn matvec4 dot4)))))

  (defthm invmixcolumn-of-mixcolumn
    (implies (wordp col) (equal (invmixcolumn (mixcolumn col)) col))
    :hints (("Goal" :use both-matrix-products-are-identity
             :in-theory (disable (:e matmul4)))))

  (defthm mixcolumn-of-invmixcolumn
    (implies (wordp col) (equal (mixcolumn (invmixcolumn col)) col))
    :hints (("Goal" :use both-matrix-products-are-identity
             :in-theory (disable (:e matmul4)))))

  (defthm invmixcolumn-of-wordxor
    (implies (and (wordp a) (wordp b))
             (equal (invmixcolumn (wordxor a b))
                    (wordxor (invmixcolumn a) (invmixcolumn b))))
    :hints (("Goal" :in-theory (enable invmixcolumn-as-matvec4
                                       matvec4-of-wordxor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Converting between states and blocks

(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))

(local (include-book "kestrel/lists-light/take" :dir :system))
(local
 (defthm list-of-four-nths
   (implies (and (true-listp x) (equal (len x) 4))
            (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x))
                   x))
   :hints (("Goal" :use (:instance acl2::take-does-nothing-simple
                           (acl2::n 4) (acl2::l x))
            :in-theory (e/d (acl2::take-opener-alt)
                            (acl2::take-does-nothing))))))

(local
 (defthm list-of-sixteen-nths
   (implies (and (true-listp x) (equal (len x) 16))
            (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)
                         (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x)
                         (nth 8 x) (nth 9 x) (nth 10 x) (nth 11 x)
                         (nth 12 x) (nth 13 x) (nth 14 x) (nth 15 x))
                   x))
   :hints (("Goal" :use (:instance acl2::take-does-nothing-simple
                           (acl2::n 16) (acl2::l x))
            :in-theory (e/d (acl2::take-opener-alt)
                            (acl2::take-does-nothing))))))

(local (in-theory (disable acl2::equal-of-cons)))

;; INP is enabled in the spec and opens to (BYTE-ARRAYP 16 ...).  Install
;; a rewrite rule for each spelling so that closure also works in theories
;; that keep INP opaque.  Preserve the INP formula for explicit :USE hints.
(defthm inp-of-copy-state-to-array
  (implies (statep s) (inp (copy-state-to-array s)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (statep s)
                      (byte-arrayp 16 (copy-state-to-array s)))))
  :hints (("Goal" :in-theory (enable inp copy-state-to-array))))

(defthm copy-state-to-array-of-copyarraytostate
  (implies (inp in)
           (equal (copy-state-to-array (copyarraytostate in)) in))
  :hints (("Goal" :in-theory (enable inp copyarraytostate copy-state-to-array
                                     array-elem-2d))))

(defthm copyarraytostate-of-copy-state-to-array
  (implies (statep s)
           (equal (copyarraytostate (copy-state-to-array s)) s))
  :hints (("Goal" :in-theory (enable copyarraytostate copy-state-to-array
                                     array-elem-2d))))

(local
 (defthm bytep-of-state-entry
   (implies (and (statep s) (natp r) (< r 4) (natp c) (< c 4))
            (bytep (nth c (nth r s))))
   :hints (("Goal" :use (:instance acl2::unsigned-byte-p-of-array-elem-2d
                                   (acl2::bytesize 8) (acl2::numrows 4)
                                   (acl2::numcols 4) (acl2::item s)
                                   (acl2::m r) (acl2::n c))
            :in-theory (e/d (array-elem-2d)
                            (acl2::unsigned-byte-p-of-array-elem-2d))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inverting the state transformations

(defthm invsubbytes-of-subbytes
  (implies (statep s) (equal (invsubbytes (subbytes s)) s))
  :hints (("Goal" :in-theory (enable subbytes invsubbytes array-elem-2d))))

(defthm subbytes-of-invsubbytes
  (implies (statep s) (equal (subbytes (invsubbytes s)) s))
  :hints (("Goal" :in-theory (enable subbytes invsubbytes array-elem-2d))))

(defthm invshiftrows-of-shiftrows
  (implies (statep s) (equal (invshiftrows (shiftrows s)) s))
  :hints (("Goal" :in-theory (enable shiftrows invshiftrows array-elem-2d))))

(defthm shiftrows-of-invshiftrows
  (implies (statep s) (equal (shiftrows (invshiftrows s)) s))
  :hints (("Goal" :in-theory (enable shiftrows invshiftrows array-elem-2d))))

;; The row permutation commutes with a uniform byte substitution.
(defthmd invshiftrows-of-invsubbytes
  (equal (invshiftrows (invsubbytes s)) (invsubbytes (invshiftrows s)))
  :hints (("Goal" :in-theory (enable invshiftrows invsubbytes array-elem-2d))))

(local
 (defthm wordp-of-state-column
   (implies (and (statep s) (natp c) (< c 4))
            (wordp (acl2::get-column c s)))))

(local
 (defthm get-columns-of-zero
   (equal (acl2::get-columns 0 a) (list (acl2::get-column 0 a)))
   :hints (("Goal" :expand ((acl2::get-columns 0 a)
                            (acl2::get-columns -1 a))))))

(local
 (defthm transpose-four-columns
   (implies (equal (len a) 4)
            (equal (acl2::transpose-2d-array (list a b c d))
                   (list (list (nth 0 a) (nth 0 b) (nth 0 c) (nth 0 d))
                         (list (nth 1 a) (nth 1 b) (nth 1 c) (nth 1 d))
                         (list (nth 2 a) (nth 2 b) (nth 2 c) (nth 2 d))
                         (list (nth 3 a) (nth 3 b) (nth 3 c) (nth 3 d)))))
   :hints (("Goal" :in-theory (enable acl2::transpose-2d-array
                                      acl2::2d-array-width acl2::get-columns
                                      acl2::reverse-list)))))

(local (in-theory (disable acl2::transpose-2d-array)))

(local
 (defthm column-of-mixcolumns
   (implies (and (natp c) (< c 4))
            (equal (acl2::get-column c (mixcolumns s))
                   (mixcolumn (acl2::get-column c s))))
   :hints (("Goal" :cases ((equal c 0) (equal c 1) (equal c 2))
            :in-theory (enable mixcolumns)))))

(local
 (defthm column-of-invmixcolumns
   (implies (and (natp c) (< c 4))
            (equal (acl2::get-column c (invmixcolumns s))
                   (invmixcolumn (acl2::get-column c s))))
   :hints (("Goal" :cases ((equal c 0) (equal c 1) (equal c 2))
            :in-theory (enable invmixcolumns)))))

(defthm invmixcolumns-of-mixcolumns
  (implies (statep s) (equal (invmixcolumns (mixcolumns s)) s))
  :hints (("Goal" :expand ((invmixcolumns (mixcolumns s)))
           :in-theory (enable array-elem-2d))))

(defthm mixcolumns-of-invmixcolumns
  (implies (statep s) (equal (mixcolumns (invmixcolumns s)) s))
  :hints (("Goal" :expand ((mixcolumns (invmixcolumns s)))
           :in-theory (enable array-elem-2d))))

;; Key bytes are chopped by BVXOR, so K needs no type hypothesis here.
(defthm addroundkey-of-addroundkey
  (implies (statep s) (equal (addroundkey (addroundkey s k) k) s))
  :hints (("Goal" :in-theory (enable addroundkey addroundkey-elem
                                     array-elem-2d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Forward and inverse rounds

(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

;; A forward round ends with AddRoundKey.  An inverse round uses its
;; key in the middle.  The forward alignment point is immediately
;; after SubBytes followed by ShiftRows.  The reverse alignment point is
;; immediately after InvShiftRows followed by InvSubBytes.

(local
 (defthm statep-of-apply-round-unconditional
   (statep (apply-round r s nk w))
   :hints (("Goal" :in-theory (enable apply-round)))))

(defthm invapply-round-of-forward-round
  (implies (statep s)
           (equal (invapply-round r (shiftrows (subbytes (apply-round r s nk w)))
                                  nk w)
                  (shiftrows (subbytes s))))
  :hints (("Goal" :in-theory (enable apply-round invapply-round))))

(defthm apply-round-of-inverse-round
  (implies (statep s)
           (equal (apply-round r (invsubbytes (invshiftrows (invapply-round r s nk w)))
                               nk w)
                  (invsubbytes (invshiftrows s))))
  :hints (("Goal" :in-theory (enable apply-round invapply-round))))

;; The forward loop counts up from r.  After the first forward round,
;; its remaining suffix has one fewer round to undo.
(local
 (defthm undo-forward-rounds-from-r
   (implies (and (statep s) (natp nk) (natp r) (<= r (nr nk)))
            (equal (invapply-rounds
                     (- (nr nk) r)
                     (shiftrows (subbytes (apply-rounds r (+ -1 (nr nk)) s nk w)))
                     w nk)
                   (shiftrows (subbytes s))))
   :hints (("Goal" :induct (apply-rounds r (+ -1 (nr nk)) s nk w)
            :in-theory (enable apply-rounds invapply-rounds)))))

(defthm invapply-rounds-of-forward-rounds
  (implies (and (statep s) (natp nk) (natp j) (< j (nr nk)))
           (equal (invapply-rounds
                    j (shiftrows
                       (subbytes (apply-rounds (- (nr nk) j) (+ -1 (nr nk)) s nk w)))
                    w nk)
                  (shiftrows (subbytes s))))
  :hints (("Goal" :use (:instance undo-forward-rounds-from-r (r (- (nr nk) j))))))

(local
 (defthm statep-of-invapply-rounds-for-any-count
   (implies (statep s) (statep (invapply-rounds j s w nk)))
   :hints (("Goal" :induct (invapply-rounds j s w nk)
            :in-theory (enable invapply-rounds)))))

(local
 (defthm apply-rounds-when-finished
   (implies (< last r) (equal (apply-rounds r last s nk w) s))
   :hints (("Goal" :expand ((apply-rounds r last s nk w))))))

(defthm apply-rounds-of-inverse-rounds
  (implies (and (statep s) (natp nk) (natp j) (< j (nr nk)))
           (equal (apply-rounds
                    (- (nr nk) j) (+ -1 (nr nk))
                    (invsubbytes (invshiftrows (invapply-rounds j s w nk)))
                    nk w)
                  (invsubbytes (invshiftrows s))))
  :hints (("Goal" :induct (invapply-rounds j s w nk)
           :in-theory (enable invapply-rounds apply-rounds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The core and block ciphers

(defthm invcipher-core-of-cipher-core
  (implies (and (statep s) (natp nk))
           (equal (invcipher-core (cipher-core s w nk) w nk) s))
  :hints (("Goal" :in-theory (enable cipher-core invcipher-core)
           :use (:instance invapply-rounds-of-forward-rounds
                           (j (+ -1 (nr nk)))
                           (s (addroundkey s (subrange 0 3 w)))))))

(defthm cipher-core-of-invcipher-core
  (implies (and (statep s) (natp nk))
           (equal (cipher-core (invcipher-core s w nk) w nk) s))
  :hints (("Goal" :in-theory (enable cipher-core invcipher-core)
           :use (:instance apply-rounds-of-inverse-rounds
                           (j (+ -1 (nr nk)))
                           (s (addroundkey s (subrange (* (nr nk) *nb*)
                                                     (+ -1 (* (+ 1 (nr nk)) *nb*))
                                                     w)))))))

(defthm inp-of-cipher
  (implies (inp in) (inp (cipher in w nk)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp in)
                      (byte-arrayp 16 (cipher in w nk))))))

(defthm inp-of-invcipher
  (implies (inp in) (inp (invcipher in w nk)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp in)
                      (byte-arrayp 16 (invcipher in w nk))))))

(defthm invcipher-of-cipher
  (implies (and (inp in) (natp nk))
           (equal (invcipher (cipher in w nk) w nk) in)))

(defthm cipher-of-invcipher
  (implies (and (inp in) (natp nk))
           (equal (cipher (invcipher in w nk) w nk) in)))

(local (in-theory (disable cipher invcipher)))

(defthm equal-of-ciphers
  (implies (and (inp x) (inp y) (natp nk))
           (equal (equal (cipher x w nk) (cipher y w nk))
                  (equal x y)))
  :hints (("Goal" :use ((:instance invcipher-of-cipher (in x))
                        (:instance invcipher-of-cipher (in y)))
           :in-theory (disable invcipher-of-cipher))))

(defthm equal-of-invciphers
  (implies (and (inp x) (inp y) (natp nk))
           (equal (equal (invcipher x w nk) (invcipher y w nk))
                  (equal x y)))
  :hints (("Goal" :use ((:instance cipher-of-invcipher (in x))
                        (:instance cipher-of-invcipher (in y)))
           :in-theory (disable cipher-of-invcipher))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Permutations of the AES block domain

;; For each key size, the first two theorems give closure on 16-byte
;; blocks.  Each onto theorem supplies both a preimage and the proof that
;; it is a block.  KEY is unrestricted in all these logical statements.

;; AES-128

(defthm inp-of-aes-128-encrypt
  (implies (inp m) (inp (aes-128-encrypt m key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp m)
                      (byte-arrayp 16 (aes-128-encrypt m key))))))

(defthm inp-of-aes-128-decrypt
  (implies (inp c) (inp (aes-128-decrypt c key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp c)
                      (byte-arrayp 16 (aes-128-decrypt c key))))))

(defthm aes-128-decrypt-of-aes-128-encrypt
  (implies (inp m) (equal (aes-128-decrypt (aes-128-encrypt m key) key) m)))

(defthm aes-128-encrypt-of-aes-128-decrypt
  (implies (inp c) (equal (aes-128-encrypt (aes-128-decrypt c key) key) c)))

;; Both maps are closed on blocks and are mutual inverses there.
(defthm aes-128-permutation-of-blocks
  (implies (inp x)
           (and (inp (aes-128-encrypt x key))
                (inp (aes-128-decrypt x key))
                (equal (aes-128-decrypt (aes-128-encrypt x key) key) x)
                (equal (aes-128-encrypt (aes-128-decrypt x key) key) x)))
  :rule-classes nil)

(defthm aes-128-encrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-128-encrypt x key) (aes-128-encrypt y key))
                  (equal x y))))

(defthm aes-128-decrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-128-decrypt x key) (aes-128-decrypt y key))
                  (equal x y))))

(defthm aes-128-encrypt-onto
  (implies (inp c)
           (and (inp (aes-128-decrypt c key))
                (equal (aes-128-encrypt (aes-128-decrypt c key) key) c)))
  :rule-classes nil)

(defthm aes-128-decrypt-onto
  (implies (inp m)
           (and (inp (aes-128-encrypt m key))
                (equal (aes-128-decrypt (aes-128-encrypt m key) key) m)))
  :rule-classes nil)

;; AES-192

(defthm inp-of-aes-192-encrypt
  (implies (inp m) (inp (aes-192-encrypt m key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp m)
                      (byte-arrayp 16 (aes-192-encrypt m key))))))

(defthm inp-of-aes-192-decrypt
  (implies (inp c) (inp (aes-192-decrypt c key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp c)
                      (byte-arrayp 16 (aes-192-decrypt c key))))))

(defthm aes-192-decrypt-of-aes-192-encrypt
  (implies (inp m) (equal (aes-192-decrypt (aes-192-encrypt m key) key) m)))

(defthm aes-192-encrypt-of-aes-192-decrypt
  (implies (inp c) (equal (aes-192-encrypt (aes-192-decrypt c key) key) c)))

;; Both maps are closed on blocks and are mutual inverses there.
(defthm aes-192-permutation-of-blocks
  (implies (inp x)
           (and (inp (aes-192-encrypt x key))
                (inp (aes-192-decrypt x key))
                (equal (aes-192-decrypt (aes-192-encrypt x key) key) x)
                (equal (aes-192-encrypt (aes-192-decrypt x key) key) x)))
  :rule-classes nil)

(defthm aes-192-encrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-192-encrypt x key) (aes-192-encrypt y key))
                  (equal x y))))

(defthm aes-192-decrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-192-decrypt x key) (aes-192-decrypt y key))
                  (equal x y))))

(defthm aes-192-encrypt-onto
  (implies (inp c)
           (and (inp (aes-192-decrypt c key))
                (equal (aes-192-encrypt (aes-192-decrypt c key) key) c)))
  :rule-classes nil)

(defthm aes-192-decrypt-onto
  (implies (inp m)
           (and (inp (aes-192-encrypt m key))
                (equal (aes-192-decrypt (aes-192-encrypt m key) key) m)))
  :rule-classes nil)

;; AES-256

(defthm inp-of-aes-256-encrypt
  (implies (inp m) (inp (aes-256-encrypt m key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp m)
                      (byte-arrayp 16 (aes-256-encrypt m key))))))

(defthm inp-of-aes-256-decrypt
  (implies (inp c) (inp (aes-256-decrypt c key)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (inp c)
                      (byte-arrayp 16 (aes-256-decrypt c key))))))

(defthm aes-256-decrypt-of-aes-256-encrypt
  (implies (inp m) (equal (aes-256-decrypt (aes-256-encrypt m key) key) m)))

(defthm aes-256-encrypt-of-aes-256-decrypt
  (implies (inp c) (equal (aes-256-encrypt (aes-256-decrypt c key) key) c)))

;; Both maps are closed on blocks and are mutual inverses there.
(defthm aes-256-permutation-of-blocks
  (implies (inp x)
           (and (inp (aes-256-encrypt x key))
                (inp (aes-256-decrypt x key))
                (equal (aes-256-decrypt (aes-256-encrypt x key) key) x)
                (equal (aes-256-encrypt (aes-256-decrypt x key) key) x)))
  :rule-classes nil)

(defthm aes-256-encrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-256-encrypt x key) (aes-256-encrypt y key))
                  (equal x y))))

(defthm aes-256-decrypt-injective
  (implies (and (inp x) (inp y))
           (equal (equal (aes-256-decrypt x key) (aes-256-decrypt y key))
                  (equal x y))))

(defthm aes-256-encrypt-onto
  (implies (inp c)
           (and (inp (aes-256-decrypt c key))
                (equal (aes-256-encrypt (aes-256-decrypt c key) key) c)))
  :rule-classes nil)

(defthm aes-256-decrypt-onto
  (implies (inp m)
           (and (inp (aes-256-encrypt m key))
                (equal (aes-256-decrypt (aes-256-encrypt m key) key) m)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; InvMixColumns and round-key addition

;; The AES spec stores a state as four rows and a round key as four
;; words, one per column.  Apply InvMixColumn to each key word directly.
(defund invmix-round-key (k)
  (declare (xargs :guard (statep k)))
  (list (invmixcolumn (nth 0 k)) (invmixcolumn (nth 1 k))
        (invmixcolumn (nth 2 k)) (invmixcolumn (nth 3 k))))

(defthm statep-of-invmix-round-key
  (statep (invmix-round-key k))
  :hints (("Goal" :in-theory (enable invmix-round-key))))

(local
 (defthm nth-of-invmix-round-key
   (implies (and (natp c) (< c 4))
            (equal (nth c (invmix-round-key k)) (invmixcolumn (nth c k))))
   :hints (("Goal" :cases ((equal c 0) (equal c 1) (equal c 2))
            :in-theory (enable invmix-round-key)))))

(local
 (defthm column-of-addroundkey
   (implies (and (natp c) (< c 4))
            (equal (acl2::get-column c (addroundkey s k))
                   (wordxor (acl2::get-column c s) (nth c k))))
   :hints (("Goal" :cases ((equal c 0) (equal c 1) (equal c 2))
            :in-theory (enable addroundkey addroundkey-elem wordxor
                               array-elem-2d)))))

(local
 (defthm state-from-its-columns
   (implies (statep s)
            (equal (acl2::transpose-2d-array
                    (list (acl2::get-column 0 s) (acl2::get-column 1 s)
                          (acl2::get-column 2 s) (acl2::get-column 3 s)))
                   s))
   :hints (("Goal" :in-theory (enable array-elem-2d)))
   :rule-classes nil))

(local
 (defthm equal-states-by-columns
   (implies (and (statep a) (statep b)
                 (equal (acl2::get-column 0 a) (acl2::get-column 0 b))
                 (equal (acl2::get-column 1 a) (acl2::get-column 1 b))
                 (equal (acl2::get-column 2 a) (acl2::get-column 2 b))
                 (equal (acl2::get-column 3 a) (acl2::get-column 3 b)))
            (equal a b))
   :hints (("Goal" :use ((:instance state-from-its-columns (s a))
                         (:instance state-from-its-columns (s b)))
            :in-theory (disable transpose-four-columns)))
   :rule-classes nil))

(defthmd invmixcolumns-of-addroundkey
  (implies (and (statep s) (statep k))
           (equal (invmixcolumns (addroundkey s k))
                  (addroundkey (invmixcolumns s) (invmix-round-key k))))
  :hints (("Goal" :use (:instance equal-states-by-columns
                                  (a (invmixcolumns (addroundkey s k)))
                                  (b (addroundkey (invmixcolumns s)
                                                  (invmix-round-key k)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The equivalent inverse cipher

;; FIPS 197 (updated 2023), section 5.3.5, Algorithms 4 and 5.
;; DW groups the expanded words by round in encryption order.  Its
;; first and last elements are the original round keys.  Every middle
;; element is a transformed round key.  DW can be reused across blocks.

(defund round-key (r w)
  (declare (xargs :guard (and (natp r) (true-listp w))))
  (subrange (* r *nb*) (+ -1 (* (+ 1 r) *nb*)) w))

(defthm statep-of-round-key
  (implies (and (expanded-keyp w nk) (natp nk) (natp r) (<= r (nr nk)))
           (statep (round-key r w)))
  :hints (("Goal" :in-theory (enable round-key expanded-keyp))))

(local
 (defthm true-listp-of-expanded-key
   (implies (expanded-keyp w nk) (true-listp w))
   :hints (("Goal" :in-theory (enable expanded-keyp)))))

(defun round-key-listp (keys)
  (declare (xargs :guard t))
  (if (consp keys)
      (and (statep (car keys)) (round-key-listp (cdr keys)))
    (equal keys nil)))

(defthm booleanp-of-round-key-listp
  (acl2::booleanp (round-key-listp keys))
  :rule-classes :type-prescription)

(defund eqinv-schedule-tail (j w nk)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8)) (expanded-keyp w nk)
                              (natp j) (< j (nr nk)))))
  (if (zp j)
      (list (round-key (nr nk) w))
    (cons (invmix-round-key (round-key (- (nr nk) j) w))
          (eqinv-schedule-tail (+ -1 j) w nk))))

(defthm round-key-listp-of-eqinv-schedule-tail
  (implies (and (natp nk) (expanded-keyp w nk))
           (round-key-listp (eqinv-schedule-tail j w nk)))
  :hints (("Goal" :induct (eqinv-schedule-tail j w nk)
           :in-theory (enable eqinv-schedule-tail))))

(defund eqinv-schedule (w nk)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8)) (expanded-keyp w nk))))
  (cons (round-key 0 w) (eqinv-schedule-tail (+ -1 (nr nk)) w nk)))

(defthm round-key-listp-of-eqinv-schedule
  (implies (and (natp nk) (expanded-keyp w nk))
           (round-key-listp (eqinv-schedule w nk)))
  :hints (("Goal" :in-theory (enable eqinv-schedule))))

(defthm len-of-eqinv-schedule-tail
  (equal (len (eqinv-schedule-tail j w nk)) (+ 1 (nfix j)))
  :hints (("Goal" :induct (eqinv-schedule-tail j w nk)
           :in-theory (enable eqinv-schedule-tail))))

(defthm len-of-eqinv-schedule
  (implies (natp nk) (equal (len (eqinv-schedule w nk)) (+ 1 (nr nk))))
  :hints (("Goal" :in-theory (enable eqinv-schedule))))

(defund eqinv-round (s mixed-key)
  (declare (xargs :guard (and (statep s) (statep mixed-key))))
  (addroundkey (invmixcolumns (invshiftrows (invsubbytes s))) mixed-key))

(defthm statep-of-eqinv-round
  (statep (eqinv-round s mixed-key))
  :hints (("Goal" :in-theory (enable eqinv-round))))

(defthm eqinv-round-is-invapply-round
  (implies (and (statep s) (statep (round-key r w)))
           (equal (eqinv-round s (invmix-round-key (round-key r w)))
                  (invapply-round r s nk w)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable eqinv-round invapply-round round-key
                                     invmixcolumns-of-addroundkey
                                     invshiftrows-of-invsubbytes))))

;; Process the tail of DW from last to first.  The last key does the
;; initial whitening.  Each remaining key supplies one interior round.
(defund eqinv-rounds (keys s)
  (declare (xargs :guard (and (consp keys) (round-key-listp keys) (statep s))
                  :verify-guards nil))
  (if (consp (cdr keys))
      (eqinv-round (eqinv-rounds (cdr keys) s) (car keys))
    (addroundkey s (car keys))))

(defthm statep-of-eqinv-rounds
  (statep (eqinv-rounds keys s))
  :hints (("Goal" :in-theory (enable eqinv-rounds))))

(acl2::verify-guards eqinv-rounds)

(defthm eqinv-rounds-is-invapply-rounds
  (implies (and (statep s) (expanded-keyp w nk) (natp nk)
                (natp j) (< j (nr nk)))
           (equal (eqinv-rounds (eqinv-schedule-tail j w nk) s)
                  (invapply-rounds j (addroundkey s (round-key (nr nk) w)) w nk)))
  :hints (("Goal" :induct (eqinv-schedule-tail j w nk)
           :in-theory (enable eqinv-schedule-tail eqinv-rounds invapply-rounds))
          ("Subgoal *1/2" :use (:instance eqinv-round-is-invapply-round
                                 (r (- (nr nk) j))
                                 (s (invapply-rounds (+ -1 j)
                                      (addroundkey s (round-key (nr nk) w)) w nk))))))

(defund eqinvcipher (in dw)
  (declare (xargs :guard (and (inp in) (round-key-listp dw)
                              (consp dw) (consp (cdr dw)))
                  :guard-hints (("Goal" :in-theory (enable inp)))))
  (let* ((s (copyarraytostate in))
         (s (eqinv-rounds (cdr dw) s))
         (s (invshiftrows (invsubbytes s)))
         (s (addroundkey s (car dw))))
    (copy-state-to-array s)))

(defthm inp-of-eqinvcipher
  (inp (eqinvcipher in dw))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (byte-arrayp 16 (eqinvcipher in dw))))
  :hints (("Goal" :in-theory (enable eqinvcipher))))

(defthm eqinvcipher-is-invcipher
  (implies (and (inp in) (expanded-keyp w nk) (natp nk))
           (equal (eqinvcipher in (eqinv-schedule w nk)) (invcipher in w nk)))
  :hints (("Goal" :in-theory (enable eqinvcipher eqinv-schedule invcipher
                                     invcipher-core round-key
                                     invshiftrows-of-invsubbytes))))
