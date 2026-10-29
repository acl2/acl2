; Equivalence of the ARRAY-SIGNATURE extracted TEA (rust_tea_arr.lisp,
; unmodified compiler output) to the Kestrel TEA spec, and the full
; all-inputs round trip. This is the array/slice milestone: the extracted
; block and key are ACL2 lists (the same representation Kestrel bv-arrays
; use), so the key array is carried through the loops unchanged -- closer
; to the spec than the scalar version.

(in-package "ACL2")

(include-book "rust_tea_arr")
(include-book "kestrel/crypto/tea/tea" :dir :system)
(include-book "kestrel/crypto/tea/inversion" :dir :system)
(include-book "tea-bridges")
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv-arrays/bv-array-read" :dir :system))
(local (include-book "kestrel/bv-arrays/bv-array-write" :dir :system))
(local (include-book "kestrel/bv-arrays/bv-arrays" :dir :system))

(local
 (defthm u32p-forward-unsigned-byte-p
   (implies (u32p x) (unsigned-byte-p 32 x))
   :hints (("Goal" :in-theory (enable u32p unsigned-byte-p)))
   :rule-classes (:forward-chaining :rewrite)))

(local
 (defthm u32-add-of-i+1-when-below-32
   (implies (and (natp i) (< i 32))
            (equal (u32-add i 1) (ok (+ i 1))))
   :hints (("Goal" :in-theory (enable u32-add u32p)))))

;; The extracted array read of a length-4 bv-array is the spec's bv-array-read.
(defthm array-index-4-is-bv-array-read
  (implies (and (bv-arrayp 32 4 k) (natp j) (< j 4))
           (equal (array-index k j) (ok (bv-array-read 32 4 j k))))
  :hints (("Goal" :in-theory (enable array-index bv-array-read bv-arrayp))))

;; ---------------------------------------------------------------------
;; Encrypt loop: one extracted round = one Kestrel round (k carried as-is).
;; ---------------------------------------------------------------------

(defthm rust-tea-arr-encrypt-loop0-step
  (implies (and (u32p y) (u32p z) (u32p sum) (bv-arrayp 32 4 k)
                (natp i) (< i 32) (natp fuel) (< 0 fuel))
           (equal (rust-tea-arr-encrypt-loop0 fuel k y z sum i)
                  (mv-let (y1 z1)
                      (tea-encrypt-loop-body y z (bvplus 32 sum *delta*) k)
                    (rust-tea-arr-encrypt-loop0 (+ -1 fuel) k y1 z1
                                                (bvplus 32 sum *delta*)
                                                (+ i 1)))))
  :hints (("Goal" :do-not-induct t
                  :expand ((rust-tea-arr-encrypt-loop0 fuel k y z sum i))
                  :in-theory (enable tea-encrypt-loop-body tea-step))))

(defthm rust-tea-arr-encrypt-loop0-at-32
  (implies (and (natp fuel) (< 0 fuel))
           (equal (rust-tea-arr-encrypt-loop0 fuel k y z sum 32)
                  (ok (cons y z))))
  :hints (("Goal" :expand ((rust-tea-arr-encrypt-loop0 fuel k y z sum 32))
                  :in-theory (disable rust-tea-arr-encrypt-loop0))))

(local
 (defun aenc-ind (n fuel y z sum i k)
   (declare (xargs :measure (nfix n)))
   (if (or (zp n) (zp fuel))
       (list y z sum i k)
     (mv-let (y1 z1) (tea-encrypt-loop-body y z (bvplus 32 sum *delta*) k)
       (aenc-ind (+ -1 n) (+ -1 fuel) y1 z1 (bvplus 32 sum *delta*)
                 (+ i 1) k)))))

(defthm rust-tea-arr-encrypt-loop0-is-spec
  (implies (and (u32p y) (u32p z) (u32p sum) (bv-arrayp 32 4 k)
                (natp n) (<= n 32) (natp fuel) (< n fuel))
           (equal (rust-tea-arr-encrypt-loop0 fuel k y z sum (- 32 n))
                  (ok (cons (mv-nth 0 (tea-encrypt-loop n y z sum k))
                            (mv-nth 1 (tea-encrypt-loop n y z sum k))))))
  :hints (("Goal" :induct (aenc-ind n fuel y z sum (- 32 n) k)
                  :in-theory (e/d (tea-encrypt-loop)
                                  (rust-tea-arr-encrypt-loop0)))))

;; ---------------------------------------------------------------------
;; Decrypt loop (sum subtracted after the body).
;; ---------------------------------------------------------------------

(defthm rust-tea-arr-decrypt-loop0-step
  (implies (and (u32p y) (u32p z) (u32p sum) (bv-arrayp 32 4 k)
                (natp i) (< i 32) (natp fuel) (< 0 fuel))
           (equal (rust-tea-arr-decrypt-loop0 fuel k y z sum i)
                  (mv-let (y1 z1)
                      (tea-decrypt-loop-body y z sum k)
                    (rust-tea-arr-decrypt-loop0 (+ -1 fuel) k y1 z1
                                                (bvminus 32 sum *delta*)
                                                (+ i 1)))))
  :hints (("Goal" :do-not-induct t
                  :expand ((rust-tea-arr-decrypt-loop0 fuel k y z sum i))
                  :in-theory (enable tea-decrypt-loop-body tea-step))))

(defthm rust-tea-arr-decrypt-loop0-at-32
  (implies (and (natp fuel) (< 0 fuel))
           (equal (rust-tea-arr-decrypt-loop0 fuel k y z sum 32)
                  (ok (cons y z))))
  :hints (("Goal" :expand ((rust-tea-arr-decrypt-loop0 fuel k y z sum 32))
                  :in-theory (disable rust-tea-arr-decrypt-loop0))))

(local
 (defun adec-ind (n fuel y z sum i k)
   (declare (xargs :measure (nfix n)))
   (if (or (zp n) (zp fuel))
       (list y z sum i k)
     (mv-let (y1 z1) (tea-decrypt-loop-body y z sum k)
       (adec-ind (+ -1 n) (+ -1 fuel) y1 z1 (bvminus 32 sum *delta*)
                 (+ i 1) k)))))

(defthm rust-tea-arr-decrypt-loop0-is-spec
  (implies (and (u32p y) (u32p z) (u32p sum) (bv-arrayp 32 4 k)
                (natp n) (<= n 32) (natp fuel) (< n fuel))
           (equal (rust-tea-arr-decrypt-loop0 fuel k y z sum (- 32 n))
                  (ok (cons (mv-nth 0 (tea-decrypt-loop n y z sum k))
                            (mv-nth 1 (tea-decrypt-loop n y z sum k))))))
  :hints (("Goal" :induct (adec-ind n fuel y z sum (- 32 n) k)
                  :in-theory (e/d (tea-decrypt-loop)
                                  (rust-tea-arr-decrypt-loop0)))))

(local
 (defthm bv-arrayp-2 (implies (and (u32p a) (u32p b)) (bv-arrayp 32 2 (list a b)))
   :hints (("Goal" :in-theory (enable bv-arrayp u32p)))))
(local
 (defthm bv-arrayp-4
   (implies (and (u32p a) (u32p b) (u32p c) (u32p d))
            (bv-arrayp 32 4 (list a b c d)))
   :hints (("Goal" :in-theory (enable bv-arrayp u32p)))))

;; ---------------------------------------------------------------------
;; Outer functions and the full round trip, over concrete blocks/keys
;; (v0 v1) / (k0..k3) -- the shape that avoids abstract-array destructuring
;; (mirrors the scalar tea-equiv.lisp). array-index on a literal list is a
;; direct nth; tea-encrypt reduces to the 2-element output list.
;; ---------------------------------------------------------------------

(defthm array-index-of-list2-0
  (equal (array-index (list a b) 0) (ok a))
  :hints (("Goal" :in-theory (enable array-index len nth))))
(defthm array-index-of-list2-1
  (equal (array-index (list a b) 1) (ok b))
  :hints (("Goal" :in-theory (enable array-index len nth))))

(defthm tea-encrypt-as-list
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3))
           (equal (tea-encrypt (list v0 v1) (list k0 k1 k2 k3))
                  (list (mv-nth 0 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3)))
                        (mv-nth 1 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3))))))
  :hints (("Goal" :in-theory (e/d (tea-encrypt bv-array-read bv-array-write
                                   update-nth2)
                                  (tea-encrypt-loop))
                  :use ((:instance tea-encrypt-loop-return-type
                                   (n 32) (y v0) (z v1) (sum 0)
                                   (k (list k0 k1 k2 k3)))))))

(defthm tea-decrypt-as-list
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3))
           (equal (tea-decrypt (list v0 v1) (list k0 k1 k2 k3))
                  (list (mv-nth 0 (tea-decrypt-loop 32 v0 v1 (bvshl 32 *delta* 5)
                                                    (list k0 k1 k2 k3)))
                        (mv-nth 1 (tea-decrypt-loop 32 v0 v1 (bvshl 32 *delta* 5)
                                                    (list k0 k1 k2 k3))))))
  :hints (("Goal" :in-theory (e/d (tea-decrypt bv-array-read bv-array-write
                                   update-nth2)
                                  (tea-decrypt-loop))
                  :use ((:instance tea-decrypt-loop-return-type
                                   (n 32) (y v0) (z v1) (sum (bvshl 32 *delta* 5))
                                   (k (list k0 k1 k2 k3)))))))

(defthm rust-tea-arr-decrypt-sum-init
  (equal (u32-wrapping-mul *rust-tea-arr-delta* 32) (ok (bvshl 32 *delta* 5)))
  :hints (("Goal" :in-theory (enable u32-wrapping-mul bvshl bvcat logapp bvchop)))
  :rule-classes nil)

(defthm rust-tea-arr-encrypt-is-spec
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (rust-tea-arr-encrypt fuel (list v0 v1) (list k0 k1 k2 k3))
                  (ok (tea-encrypt (list v0 v1) (list k0 k1 k2 k3)))))
  :hints (("Goal" :in-theory (e/d (rust-tea-arr-encrypt tea-encrypt-as-list)
                                  (tea-encrypt tea-encrypt-loop))
                  :use ((:instance rust-tea-arr-encrypt-loop0-is-spec
                                   (n 32) (y v0) (z v1) (sum 0)
                                   (k (list k0 k1 k2 k3)))))))

(defthm rust-tea-arr-decrypt-is-spec
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (rust-tea-arr-decrypt fuel (list v0 v1) (list k0 k1 k2 k3))
                  (ok (tea-decrypt (list v0 v1) (list k0 k1 k2 k3)))))
  :hints (("Goal" :in-theory (e/d (rust-tea-arr-decrypt tea-decrypt-as-list)
                                  (tea-decrypt tea-decrypt-loop))
                  :use ((:instance rust-tea-arr-decrypt-loop0-is-spec
                                   (n 32) (y v0) (z v1) (sum (bvshl 32 *delta* 5))
                                   (k (list k0 k1 k2 k3)))
                        rust-tea-arr-decrypt-sum-init))))

;; THE PAYOFF (array API): decrypt(encrypt(v,k),k) = v for all inputs,
;; proved for the UNMODIFIED array-in/array-out extracted Rust code.
(defthm rust-tea-arr-decrypt-of-encrypt
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (b* (((ok c) (rust-tea-arr-encrypt fuel (list v0 v1)
                                                     (list k0 k1 k2 k3))))
                    (rust-tea-arr-decrypt fuel c (list k0 k1 k2 k3)))
                  (ok (list v0 v1))))
  :hints (("Goal" :in-theory (e/d (rust-tea-arr-encrypt-is-spec
                                   rust-tea-arr-decrypt-is-spec)
                                  (rust-tea-arr-encrypt rust-tea-arr-decrypt))
                  :use ((:instance tea-decrypt-of-tea-encrypt
                                   (v (list v0 v1)) (k (list k0 k1 k2 k3)))))))
