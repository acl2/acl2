; Rules for lifting
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "read-and-write")
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "../priorities")
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(add-known-boolean in-region32p)
(add-known-boolean subregion32p)
(add-known-boolean disjoint-regions32p)

(add-known-boolean stat32ip)

(def-constant-opener in-region32p)
(def-constant-opener subregion32p)
(def-constant-opener disjoint-regions32p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-constant-opener riscv::decodex)
(def-constant-opener ubyte32-fix)
(def-constant-opener ubyte32p)
(def-constant-opener riscv::get-fields-itype)
(def-constant-opener riscv::get-fields-jtype)
(def-constant-opener riscv::get-rd)
(def-constant-opener riscv::get-rs1)
(def-constant-opener riscv::get-rs2)
(def-constant-opener riscv::get-funct3)
(def-constant-opener riscv::get-funct7)

(def-constant-opener riscv::get-opcode)
(def-constant-opener riscv::get-imm-btype)
(def-constant-opener riscv::get-imm-itype)
(def-constant-opener riscv::get-imm-jtype)
(def-constant-opener riscv::get-imm-stype)
(def-constant-opener riscv::get-imm-utype)
(def-constant-opener bitops::part-select-low-high$inline)
(def-constant-opener bitops::part-select-width-low$inline)
(def-constant-opener riscv::feat-64p)
(def-constant-opener riscv::get-fields-rtype)
(def-constant-opener riscv::get-fields-btype)
(def-constant-opener riscv::get-fields-utype)
(def-constant-opener riscv::get-fields-stype)
(def-constant-opener riscv::feat->m$inline)

(def-constant-opener logtail$inline)
(def-constant-opener expt2$inline)
(def-constant-opener ifloor$inline)
(def-constant-opener logapp)
(def-constant-opener binary-logand)
(def-constant-opener ash)

(def-constant-opener riscv::instr-op-imm)
(def-constant-opener riscv::op-imm-funct-kind$inline)

(def-constant-opener riscv::instr-store)
(def-constant-opener riscv::instr-load)
(def-constant-opener riscv::instr-op)


;todo: more
(defopeners exec32-op-imm :hyps ((syntaxp (quotep riscv::funct))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move and gen

;; may help with sbox lookup, etc.
(defthm in-region32p-byte-special
  (implies (and (unsigned-byte-p 8 x)
                (<= 256 len)
                (natp len))
           (in-region32p x len 0))
  :hints (("Goal" :in-theory (enable in-region32p bvlt))))

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
           (disjoint-regions32p 1 byte len ad))
  :hints (("Goal" :in-theory (enable disjoint-regions32p bvlt bvminus unsigned-byte-p acl2::bvchop-of-sum-cases))))

;move acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version out of axe/rules3.

;;special case for isize=8
(defthmd bv-array-read-shorten-8
  (implies (and (unsigned-byte-p 8 index)
                (< (expt 2 8) len)
                (equal len (len data)))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size (expt 2 8) index (take (expt 2 8) data))))
  :hints (("Goal" :use (:instance acl2::bv-array-read-shorten-core (isize 8) (index index) (data data) (element-size element-size))
           :in-theory (disable acl2::bv-array-read-shorten-core))))

;; todo: arrange to (safely) eval binary-logand

(defthm not-in-region32p-when-disjoint-regions32p-special
  (implies (and (disjoint-regions32p len1 ad1 len2 ad) ; ad here is the same as in the lhs
                (posp len2)
                (subregion32p len start len1 ad1))
           (not (in-region32p ad len start))))


(defun bvlt-alias (size x y) (bvlt size x y))

(defthm show-unresolved-bvlt
  (implies (bvlt-alias size x y)
           (bvlt size x y)))
;; try very late
(acl2::set-axe-rule-priority show-unresolved-bvlt 10)


;;(thm (not (bvlt '32 (bvplus '32 '4294960416 (bvxor '8 x y)) '4)))

(defthm <-of-read-linear
  (implies (natp n)
           (< (read n addr stat) (expt 2 (* 8 n))))
  :rule-classes :linear
  :hints (("Goal" :use (unsigned-byte-p-of-read-simple)
           :in-theory (disable unsigned-byte-p-of-read
                               unsigned-byte-p-of-read-simple))))

(defthm bvlt-of-read-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)
                              (quotep n)))
                (<= (expt 2 (* 8 n)) (bvchop size k))
                (natp n)
                (natp size))
           (bvlt size (read n addr stat) k))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm step32-of-if
  (equal (step32 (if test x y))
         (if test (step32 x) (step32 y))))
