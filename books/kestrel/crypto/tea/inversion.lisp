; Inversion proof for TEA
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tea")
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for the bvmult-of-bvplus rules
(local (include-book "kestrel/bv/convert-to-bv-rules" :dir :system))
(local (include-book "kestrel/bv-lists/packbv-and-unpackbv" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/axe/rules1" :dir :system)) ; for bv-array-write-equal-rewrite-alt

;; Inversion
(defthm pack-tea-input-of-unpack-tea-output
  (implies (bv-arrayp 32 2 ints)
           (equal (pack-tea-input (unpack-tea-output ints))
                  ints))
  :hints (("Goal" :in-theory (enable pack-tea-input unpack-tea-output))))

;; Inversion
(defthm unpack-tea-output-of-pack-tea-input
  (implies (and (unsigned-byte-listp 8 bytes)
                (= 8 (len bytes)))
           (equal (unpack-tea-output (pack-tea-input bytes))
                  bytes))
  :hints (("Goal" :in-theory (enable pack-tea-input unpack-tea-output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defund tea-encrypt-loop-i (n y z sum k)
   (declare (xargs :guard (and (unsigned-byte-p 32 n) ;n<=32
                               (unsigned-byte-p 32 y)
                               (unsigned-byte-p 32 z)
                               (unsigned-byte-p 32 sum)
                               (bv-arrayp 32 4 k))))
   (if (zp n)
       (mv y z)
     (let ((n (+ -1 n))
           (sum (bvplus 32 sum *delta*)))
       (mv-let (y z)
           (tea-encrypt-loop-body y z sum k)
         (tea-encrypt-loop-i n y z sum k))))))

(local
 (defthmd tea-encrypt-loop-opener
   (implies (not (zp n))
            (equal (tea-encrypt-loop n y z sum k)
                   (mv-let (y z)
                       (tea-encrypt-loop (+ -1 n) y z sum k)
                     ;; the mv-let and mv here are not strictly necessary:
                     (mv-let (y z)
                         (tea-encrypt-loop-body y z (bvplus 32 sum (bvmult 32 n *delta*)) k)
                       (mv y z)))))
   :hints (("Goal" :expand ((:free (y z sum k) (tea-encrypt-loop n y z sum k))
                            (:free (y z sum k) (tea-encrypt-loop (+ -1 n) y z sum k))
                            (:free (y z sum k) (tea-encrypt-loop 0 y z sum k)))
                   :induct (tea-encrypt-loop-i n y z sum k)
                   :in-theory (enable (:I tea-encrypt-loop-i)
                                      tea-encrypt-loop
                                      bvmult-convert-arg3-to-bv
                                      trim-of-+-becomes-bvplus ;todo: needs to be enabled if we have the convert rules
                                      )))))

;; Inversion of the loop body
(local
 (defthm tea-decrypt-loop-body-of-tea-encrypt-loop-body
   (implies (and (unsigned-byte-p 32 y)
                 (unsigned-byte-p 32 z)
                 (unsigned-byte-p 32 sum)
                 (bv-arrayp 32 4 k))
            (equal (tea-decrypt-loop-body (mv-nth 0 (tea-encrypt-loop-body y z sum k))
                                          (mv-nth 1 (tea-encrypt-loop-body y z sum k))
                                          sum k)
                   (mv y z)))
   :hints (("Goal" :in-theory (enable tea-encrypt-loop-body tea-decrypt-loop-body)))))

(local
 (defund tea-encrypt-loop-i2 (n y z sum k)
   (declare (xargs :guard (and (unsigned-byte-p 32 n) ;n<=32
                               (unsigned-byte-p 32 y)
                               (unsigned-byte-p 32 z)
                               (unsigned-byte-p 32 sum)
                               (bv-arrayp 32 4 k))))
   (if (zp n)
       (mv y z)
     (let ((n (+ -1 n))
           ;;(sum (bvplus 32 sum *delta*))
           )
       (tea-encrypt-loop-i2 n y z sum k)))))

(local
 (defthm tea-encrypt-loop-base
   (implies (zp n)
            (equal (tea-encrypt-loop n y z sum k)
                   (mv y z)))
   :hints (("Goal" :in-theory (enable tea-encrypt-loop)))))

;; Inversion of the loop
(local
 (defthm tea-decrypt-loop-of-tea-encrypt-loop
   (implies (and (unsigned-byte-p 32 y)
                 (unsigned-byte-p 32 z)
                 (unsigned-byte-p 32 sum)
                 (bv-arrayp 32 4 k))
            (equal (tea-decrypt-loop n
                                     (mv-nth 0 (tea-encrypt-loop n y z sum k))
                                     (mv-nth 1 (tea-encrypt-loop n y z sum k))
                                     ;; the tricky part (the first value of SUM used during decryption must be
                                     ;; the last value of SUM used during encryption):
                                     (bvplus 32 sum (bvmult 32 n *delta*))
                                     k)
                   (mv y z)))
   :hints (("Goal" :in-theory (e/d (tea-decrypt-loop (:i tea-encrypt-loop)
                                                     (:i tea-encrypt-loop-i2)
                                                     tea-encrypt-loop-opener
                                                     bvmult-convert-arg3-to-bv
                                                     trim-of-+-becomes-bvplus)
                                   ((:d tea-encrypt-loop) tea-decrypt-loop))
                   :induct (tea-encrypt-loop-i2 n y z sum k)
                   :expand ((:free (y z sum k) (tea-decrypt-loop n y z sum k)))))))

;; Inversion
(defthm tea-decrypt-of-tea-encrypt
  (implies (and (bv-arrayp 32 2 v)
                (bv-arrayp 32 4 k))
           (equal (tea-decrypt (tea-encrypt v k) k)
                  v))
  :hints (("Goal" :use ((:instance tea-decrypt-loop-of-tea-encrypt-loop
                                   (y (bv-array-read 32 2 0 v))
                                   (z (bv-array-read 32 2 1 v))
                                   (sum 0)
                                   (n 32)))
                  :in-theory (e/d (tea-encrypt tea-decrypt) (tea-decrypt-loop-of-tea-encrypt-loop)))))

;; Inversion
(defthm tea-decrypt-spec-of-tea-encrypt-spec
  (implies (and (unsigned-byte-listp 8 key)
                (= 16 (len key))
                (unsigned-byte-listp 8 input)
                (= 8 (len input)))
           (equal (tea-decrypt-spec key (tea-encrypt-spec key input))
                  input))
  :hints (("Goal" :in-theory (enable tea-encrypt-spec tea-decrypt-spec))))
