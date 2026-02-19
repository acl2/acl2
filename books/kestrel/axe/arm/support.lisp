; Support for proofs about 32-bit ARM code
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

(include-book "portcullis")
(include-book "kestrel/arm/memory32" :dir :system)
(include-book "kestrel/arm/decoder" :dir :system)
(include-book "kestrel/arm/memory" :dir :system)
(include-book "kestrel/arm/step" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "kestrel/bv-lists/bv-list-read-chunk-little" :dir :system)

(def-constant-opener arm::in-region32p)
(def-constant-opener arm::subregion32p)
(def-constant-opener arm::disjoint-regions32p)

(add-known-boolean arm::in-region32p)
(add-known-boolean arm::subregion32p)
(add-known-boolean arm::disjoint-regions32p)

(def-constant-opener arm::arm32-decode)

;; may help with sbox lookup, etc.
;; (defthm in-region32p-byte-special
;;   (implies (and (unsigned-byte-p 8 x)
;;                 (<= 256 len)
;;                 (natp len))
;;            (arm::in-region32p x len 0))
;;   :hints (("Goal" :in-theory (enable arm::in-region32p bvlt))))

(defthm disjoint-regions32p-byte-special
  (implies (and (syntaxp (and (quotep ad)
                              (quotep len)))
                (unsigned-byte-p 32 len)
                (unsigned-byte-p 32 ad)
                (bvlt 32 255 ad)
                (bvle 32 len (bvminus 32 (+ -1 (expt 2 32)) ad))
                (integerp ad)
                (natp len)
                (unsigned-byte-p 8 byte))
           (arm::disjoint-regions32p 1 byte len ad))
  :hints (("Goal" :in-theory (enable arm::disjoint-regions32p bvlt bvminus unsigned-byte-p acl2::bvchop-of-sum-cases))))

(defthm not-in-region32p-when-disjoint-regions32p-special
  (implies (and (arm::disjoint-regions32p len1 ad1 len2 ad) ; ad here is the same as in the lhs
                (posp len2)
                (arm::subregion32p len start len1 ad1))
           (not (arm::in-region32p ad len start))))

;dup
(defthm <-of-read-linear
  (implies (natp n)
           (< (read n addr arm) (expt 2 (* 8 n))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance arm::unsigned-byte-p-of-read-simple (arm::n n) (arm::addr addr)))
                  :in-theory (e/d (unsigned-byte-p)
                                  (arm::unsigned-byte-p-of-read
                                   arm::unsigned-byte-p-of-read-simple)))))

;dup
(defthm bvlt-of-read-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)
                              (quotep n)))
                (<= (expt 2 (* 8 n)) (bvchop size k))
                (natp n)
                (natp size))
           (bvlt size (read n addr arm) k))
  :hints (("Goal" :in-theory (enable bvlt))))

;; Open when the instruction is known
(defopeners arm::execute-inst
    :hyps ((syntaxp (and (quotep arm::mnemonic)
                         (quotep args)))))

(defopeners arm::pop-loop)

(defopeners arm::push-loop)

(def-constant-opener bvcount)

;replace the other
(defthm arm::set-reg-of-set-reg-diff-2
  (implies (and (syntaxp (and (quotep reg1)
                              (quotep reg2)))
                (< reg2 reg1)
                (arm::register-numberp reg2)
                (arm::register-numberp reg1))
           (equal (set-reg reg1 val1 (set-reg reg2 val2 stat))
                  (set-reg reg2 val2 (set-reg reg1 val1 stat))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" ;:use write32-xreg-of-write32-xreg-diff-helper
           :in-theory (enable))))
