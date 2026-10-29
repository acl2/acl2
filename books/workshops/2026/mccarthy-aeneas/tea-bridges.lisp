; Op bridges book (see tea-equiv.lisp). arithmetic-5 is confined here.
; Equivalence of the COMPILER-GENERATED TEA (gen-tea.lisp) to the Kestrel
; TEA specification (books/kestrel/crypto/tea).  Proving this lets us
; inherit Kestrel's already-proved inversion theorem
;   (tea-decrypt (tea-encrypt v k) k) = v
; for the extracted code, i.e. the full all-inputs round trip.

(in-package "ACL2")

(include-book "rust_tea")
(include-book "kestrel/crypto/tea/tea" :dir :system)
(include-book "kestrel/crypto/tea/inversion" :dir :system)
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "kestrel/bv/bvshl" :dir :system))
(local (include-book "kestrel/bv/bvshr" :dir :system))
(local (include-book "kestrel/bv/logxor-b" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;; u32 values are already 32-bit, so bvchop is the identity on them.
(defthm u32p-is-unsigned-byte-p-32
  (equal (u32p x) (unsigned-byte-p 32 x))
  :hints (("Goal" :in-theory (enable u32p unsigned-byte-p))))

(local
 (defthm ubp32-implies-bvchop-32
   (implies (unsigned-byte-p 32 x) (equal (bvchop 32 x) x))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(local
 (defthm u32p-forward-unsigned-byte-p
   (implies (u32p x) (unsigned-byte-p 32 x))
   :hints (("Goal" :in-theory (enable u32p unsigned-byte-p)))
   :rule-classes :forward-chaining))

;; ---------------------------------------------------------------------
;; Op-level bridge: the extracted u32 ops equal the spec's bit-vector ops
;; on u32 inputs.
;; ---------------------------------------------------------------------

(defthmd u32-wrapping-add-is-bvplus
  (implies (and (integerp x) (integerp y))
           (equal (u32-wrapping-add x y) (ok (bvplus 32 x y))))
  :hints (("Goal" :in-theory (enable u32-wrapping-add bvplus bvchop))))

(defthmd u32-wrapping-sub-is-bvminus
  (implies (and (integerp x) (integerp y))
           (equal (u32-wrapping-sub x y) (ok (bvminus 32 x y))))
  :hints (("Goal" :in-theory (enable u32-wrapping-sub bvminus bvchop))))

(defthmd u32-xor-is-bvxor
  (implies (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
           (equal (u32-xor x y) (bvxor 32 x y)))
  :hints (("Goal" :in-theory (enable u32-xor bvxor))))

(defthmd u32-shl-4-is-bvshl
  (implies (unsigned-byte-p 32 x)
           (equal (u32-shl x 4) (ok (bvshl 32 x 4))))
  :hints (("Goal" :in-theory (enable u32-shl bvshl bvcat logapp bvchop unsigned-byte-p))))

(defthmd u32-shr-5-is-bvshr
  (implies (unsigned-byte-p 32 x)
           (equal (u32-shr x 5) (ok (bvshr 32 x 5))))
  :hints (("Goal" :in-theory (enable u32-shr bvshr slice logtail bvchop unsigned-byte-p))))


;; Export the op bridges as enabled rewrite rules for the equivalence book.
(in-theory (enable u32-wrapping-add-is-bvplus u32-wrapping-sub-is-bvminus
                   u32-xor-is-bvxor u32-shl-4-is-bvshl u32-shr-5-is-bvshr))
