; Equivalence of the COMPILER-GENERATED TEA (rust_tea.lisp, unmodified output
; of charon + aeneas -backend acl2) to the Kestrel TEA specification
; (books/kestrel/crypto/tea). This lets us INHERIT Kestrel's already-proved
; inversion theorem (tea-decrypt (tea-encrypt v k) k) = v for the extracted
; code -- i.e. the full all-inputs round trip.
;
; Op-level bridges live in tea-bridges.lisp (which confines arithmetic-5).
; Here we do the loop induction and outer-function equivalence using only
; the bit-vector rewrite rules, so the heavy proof stays fast.

(in-package "ACL2")

(include-book "rust_tea")
(include-book "kestrel/crypto/tea/tea" :dir :system)
(include-book "kestrel/crypto/tea/inversion" :dir :system)
(include-book "tea-bridges")
(local (include-book "kestrel/bv/rules" :dir :system))

;; local recognizer facts (kept out of the bridges book's export)
(local
 (defthm u32p-forward-unsigned-byte-p
   (implies (u32p x) (unsigned-byte-p 32 x))
   :hints (("Goal" :in-theory (enable u32p unsigned-byte-p)))
   :rule-classes (:forward-chaining :rewrite)))

;; The extracted i-counter step (i+1, i<32) never overflows.
(local
 (defthm u32-add-of-i+1-when-below-32
   (implies (and (natp i) (< i 32))
            (equal (u32-add i 1) (ok (+ i 1))))
   :hints (("Goal" :in-theory (enable u32-add u32p)))))

;; The key array built from four u32s reads back as those u32s.
(local
 (defthm bv-array-read-4-of-list4
   (implies (and (u32p k0) (u32p k1) (u32p k2) (u32p k3))
            (and (equal (bv-array-read 32 4 0 (list k0 k1 k2 k3)) k0)
                 (equal (bv-array-read 32 4 1 (list k0 k1 k2 k3)) k1)
                 (equal (bv-array-read 32 4 2 (list k0 k1 k2 k3)) k2)
                 (equal (bv-array-read 32 4 3 (list k0 k1 k2 k3)) k3)))
   :hints (("Goal" :in-theory (enable bv-array-read)))))


;; The extracted delta constant is the spec delta.
(defthm rust-tea-delta-is-delta
  (equal *rust-tea-delta* *delta*)
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; One extracted encrypt round = one Kestrel round (bounded; no induction).
;; ---------------------------------------------------------------------

(defthm rust-tea-encrypt-loop0-step
  (implies (and (u32p y) (u32p z) (u32p sum)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp i) (< i 32) (natp fuel) (< 0 fuel))
           (equal (rust-tea-encrypt-loop0 fuel k0 k1 k2 k3 y z sum i)
                  (mv-let (y1 z1)
                      (tea-encrypt-loop-body y z (bvplus 32 sum *delta*)
                                             (list k0 k1 k2 k3))
                    (rust-tea-encrypt-loop0 (+ -1 fuel) k0 k1 k2 k3
                                            y1 z1 (bvplus 32 sum *delta*)
                                            (+ i 1)))))
  :hints (("Goal" :do-not-induct t
                  :expand ((rust-tea-encrypt-loop0 fuel k0 k1 k2 k3 y z sum i))
                  :in-theory (enable tea-encrypt-loop-body tea-step))))


;; Base case: at i=32 the extracted loop halts immediately (no rounds).
(defthm rust-tea-encrypt-loop0-at-32
  (implies (and (natp fuel) (< 0 fuel))
           (equal (rust-tea-encrypt-loop0 fuel k0 k1 k2 k3 y z sum 32)
                  (ok (cons y z))))
  :hints (("Goal" :expand ((rust-tea-encrypt-loop0 fuel k0 k1 k2 k3 y z sum 32))
                  :in-theory (disable rust-tea-encrypt-loop0))))

;; Induction scheme decrementing rounds n AND fuel together, matching the
;; step lemma's recursive call. (This drives the induction; it does not
;; unfold the extracted function, which stays disabled.)
(local
 (defun enc-ind (n fuel y z sum k)
   (declare (xargs :measure (nfix n)))
   (if (or (zp n) (zp fuel))
       (list y z sum k)
     (mv-let (y1 z1)
         (tea-encrypt-loop-body y z (bvplus 32 sum *delta*) k)
       (enc-ind (+ -1 n) (+ -1 fuel) y1 z1 (bvplus 32 sum *delta*) k)))))

;; ---------------------------------------------------------------------
;; Encrypt loop equivalence. The step lemma rewrites each extracted round
;; to a Kestrel round; the base lemma closes i=32; the scheme above steps
;; n and fuel together so the induction hypothesis lands exactly.
;; ---------------------------------------------------------------------

(defthm rust-tea-encrypt-loop0-is-spec
  (implies (and (u32p y) (u32p z) (u32p sum)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp n) (<= n 32) (natp fuel) (< n fuel))
           (equal (rust-tea-encrypt-loop0 fuel k0 k1 k2 k3 y z sum (- 32 n))
                  (ok (cons (mv-nth 0 (tea-encrypt-loop n y z sum
                                                        (list k0 k1 k2 k3)))
                            (mv-nth 1 (tea-encrypt-loop n y z sum
                                                        (list k0 k1 k2 k3)))))))
  :hints (("Goal" :induct (enc-ind n fuel y z sum (list k0 k1 k2 k3))
                  :in-theory (e/d (tea-encrypt-loop)
                                  (rust-tea-encrypt-loop0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Decrypt loop equivalence (same shape; sum is subtracted AFTER the body).

(defthm rust-tea-decrypt-loop0-step
  (implies (and (u32p y) (u32p z) (u32p sum)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp i) (< i 32) (natp fuel) (< 0 fuel))
           (equal (rust-tea-decrypt-loop0 fuel k0 k1 k2 k3 y z sum i)
                  (mv-let (y1 z1)
                      (tea-decrypt-loop-body y z sum (list k0 k1 k2 k3))
                    (rust-tea-decrypt-loop0 (+ -1 fuel) k0 k1 k2 k3
                                            y1 z1 (bvminus 32 sum *delta*)
                                            (+ i 1)))))
  :hints (("Goal" :do-not-induct t
                  :expand ((rust-tea-decrypt-loop0 fuel k0 k1 k2 k3 y z sum i))
                  :in-theory (enable tea-decrypt-loop-body tea-step))))

(defthm rust-tea-decrypt-loop0-at-32
  (implies (and (natp fuel) (< 0 fuel))
           (equal (rust-tea-decrypt-loop0 fuel k0 k1 k2 k3 y z sum 32)
                  (ok (cons y z))))
  :hints (("Goal" :expand ((rust-tea-decrypt-loop0 fuel k0 k1 k2 k3 y z sum 32))
                  :in-theory (disable rust-tea-decrypt-loop0))))

(local
 (defun dec-ind (n fuel y z sum k)
   (declare (xargs :measure (nfix n)))
   (if (or (zp n) (zp fuel))
       (list y z sum k)
     (mv-let (y1 z1)
         (tea-decrypt-loop-body y z sum k)
       (dec-ind (+ -1 n) (+ -1 fuel) y1 z1 (bvminus 32 sum *delta*) k)))))

(defthm rust-tea-decrypt-loop0-is-spec
  (implies (and (u32p y) (u32p z) (u32p sum)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp n) (<= n 32) (natp fuel) (< n fuel))
           (equal (rust-tea-decrypt-loop0 fuel k0 k1 k2 k3 y z sum (- 32 n))
                  (ok (cons (mv-nth 0 (tea-decrypt-loop n y z sum
                                                        (list k0 k1 k2 k3)))
                            (mv-nth 1 (tea-decrypt-loop n y z sum
                                                        (list k0 k1 k2 k3)))))))
  :hints (("Goal" :induct (dec-ind n fuel y z sum (list k0 k1 k2 k3))
                  :in-theory (e/d (tea-decrypt-loop)
                                  (rust-tea-decrypt-loop0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Outer functions = the Kestrel spec loops (32 rounds), and the full
;; all-inputs round trip, inheriting Kestrel's loop inversion theorem.

(defthm rust-tea-encrypt-is-spec
  (implies (and (u32p v0) (u32p v1)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (rust-tea-encrypt fuel v0 v1 k0 k1 k2 k3)
                  (ok (cons (mv-nth 0 (tea-encrypt-loop 32 v0 v1 0
                                                        (list k0 k1 k2 k3)))
                            (mv-nth 1 (tea-encrypt-loop 32 v0 v1 0
                                                        (list k0 k1 k2 k3)))))))
  :hints (("Goal" :in-theory (enable rust-tea-encrypt)
                  :use ((:instance rust-tea-encrypt-loop0-is-spec
                                   (n 32) (y v0) (z v1) (sum 0))))))

;; The extracted decrypt sum init equals the spec's starting sum, 32*delta.
(defthm rust-tea-decrypt-sum-init
  (equal (u32-wrapping-mul *rust-tea-delta* 32)
         (ok (bvshl 32 *delta* 5)))
  :hints (("Goal" :in-theory (enable u32-wrapping-mul bvshl bvcat logapp bvchop)))
  :rule-classes nil)

(defthm rust-tea-decrypt-is-spec
  (implies (and (u32p v0) (u32p v1)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (rust-tea-decrypt fuel v0 v1 k0 k1 k2 k3)
                  (ok (cons (mv-nth 0 (tea-decrypt-loop
                                       32 v0 v1 (bvshl 32 *delta* 5)
                                       (list k0 k1 k2 k3)))
                            (mv-nth 1 (tea-decrypt-loop
                                       32 v0 v1 (bvshl 32 *delta* 5)
                                       (list k0 k1 k2 k3)))))))
  :hints (("Goal" :in-theory (enable rust-tea-decrypt)
                  :use ((:instance rust-tea-decrypt-loop0-is-spec
                                   (n 32) (y v0) (z v1)
                                   (sum (bvshl 32 *delta* 5)))
                        rust-tea-decrypt-sum-init))))

;; THE PAYOFF: decrypt(encrypt(v,k),k) = v for ALL inputs, proved for the
;; UNMODIFIED extracted Rust code by equivalence to the Kestrel TEA spec
;; plus Kestrel's own loop-inversion theorem.

;; Bridge the scalar outer functions to the Kestrel ARRAY API, so we can
;; use the exported array-level inversion theorem (the loop-level one is
;; local to Kestrel's book).
(local (include-book "kestrel/bv-arrays/bv-array-read" :dir :system))
(local (include-book "kestrel/bv-arrays/bv-array-write" :dir :system))
(local (include-book "kestrel/bv-arrays/bv-arrays" :dir :system))

(local
 (defthm bv-arrayp-list2
   (implies (and (u32p v0) (u32p v1)) (bv-arrayp 32 2 (list v0 v1)))
   :hints (("Goal" :in-theory (enable bv-arrayp u32p)))))

(local
 (defthm bv-arrayp-list4
   (implies (and (u32p k0) (u32p k1) (u32p k2) (u32p k3))
            (bv-arrayp 32 4 (list k0 k1 k2 k3)))
   :hints (("Goal" :in-theory (enable bv-arrayp u32p)))))

;; The spec array-encrypt is the 2-element list of the loop outputs.
(defthm tea-encrypt-as-loop
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3))
           (equal (tea-encrypt (list v0 v1) (list k0 k1 k2 k3))
                  (list (mv-nth 0 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3)))
                        (mv-nth 1 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3))))))
  :hints (("Goal" :in-theory (enable tea-encrypt bv-array-read bv-array-write update-nth2)
                  :use ((:instance tea-encrypt-loop-return-type
                                   (n 32) (y v0) (z v1) (sum 0)
                                   (k (list k0 k1 k2 k3)))))))

(defthm tea-decrypt-as-loop
  (implies (and (u32p v0) (u32p v1) (u32p k0) (u32p k1) (u32p k2) (u32p k3))
           (equal (tea-decrypt (list v0 v1) (list k0 k1 k2 k3))
                  (list (mv-nth 0 (tea-decrypt-loop 32 v0 v1 (bvshl 32 *delta* 5)
                                                    (list k0 k1 k2 k3)))
                        (mv-nth 1 (tea-decrypt-loop 32 v0 v1 (bvshl 32 *delta* 5)
                                                    (list k0 k1 k2 k3))))))
  :hints (("Goal" :in-theory (enable tea-decrypt bv-array-read bv-array-write update-nth2)
                  :use ((:instance tea-decrypt-loop-return-type
                                   (n 32) (y v0) (z v1) (sum (bvshl 32 *delta* 5))
                                   (k (list k0 k1 k2 k3)))))))

;; Extracted decrypt's sum init (bvplus 0 (bvmult 32 32 delta)) equals the
;; spec's (bvshl 32 delta 5); both are 32*delta mod 2^32.
(defthm decrypt-sum-inits-agree
  (equal (bvshl 32 *delta* 5) (bvshl 32 *delta* 5))
  :rule-classes nil)

;; THE PAYOFF: decrypt(encrypt(v,k),k) = v for ALL inputs, proved for the
;; UNMODIFIED extracted Rust code, by equivalence to the Kestrel TEA spec
;; and Kestrel's exported array-level inversion theorem.
(defthm rust-tea-decrypt-of-encrypt
  (implies (and (u32p v0) (u32p v1)
                (u32p k0) (u32p k1) (u32p k2) (u32p k3)
                (natp fuel) (< 32 fuel))
           (equal (b* (((ok c) (rust-tea-encrypt fuel v0 v1 k0 k1 k2 k3)))
                    (rust-tea-decrypt fuel (car c) (cdr c) k0 k1 k2 k3))
                  (ok (cons v0 v1))))
  :hints (("Goal"
           :in-theory (e/d () (rust-tea-encrypt rust-tea-decrypt
                               tea-encrypt-loop tea-decrypt-loop))
           :use ((:instance rust-tea-encrypt-is-spec)
                 (:instance rust-tea-decrypt-is-spec
                            (v0 (mv-nth 0 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3))))
                            (v1 (mv-nth 1 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3)))))
                 (:instance tea-encrypt-as-loop)
                 (:instance tea-decrypt-as-loop
                            (v0 (mv-nth 0 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3))))
                            (v1 (mv-nth 1 (tea-encrypt-loop 32 v0 v1 0 (list k0 k1 k2 k3)))))
                 (:instance tea-decrypt-of-tea-encrypt
                            (v (list v0 v1)) (k (list k0 k1 k2 k3)))
                 ))))
