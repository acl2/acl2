; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "app-view/user-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "init" :ttags :all)
(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* (rime-size
                         rme-size
                         wime-size
                         wme-size)
                        (mv-nth-1-wb-and-!flgi-commute
                         ia32e-la-to-pa-values-and-!flgi
                         las-to-pas
                         las-to-pas-values-and-!flgi
                         mv-nth-2-las-to-pas-and-!flgi-not-ac-commute
                         xr-fault-wb-in-system-level-marking-view
                         xr-fault-wb-in-sys-view))))

;; ======================================================================

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why one-read-with-rb-from-program-at)
;; (acl2::why program-at-wb-disjoint)

(defthmd effects-copyData-loop-base
  (implies
   (and (equal m 4)
        (loop-preconditions k m addr src-addr dst-addr x86))
   (equal (x86-run (loop-clk-base) x86)
          (XW
           :RGF *RAX* 0
           (XW
            :RGF *RCX*
            (MV-NTH 1 (RB 4 (XR :RGF *RDI* X86) :R X86))
            (XW
             :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
             (XW
              :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
              (XW
               :RIP 0 (+ 18 (XR :RIP 0 X86))
               (MV-NTH
                1
                (WB
                 4 (XR :RGF *RSI* X86)
                 :W
                 (MV-NTH 1 (RB 4 (XR :RGF *RDI* X86) :R X86))
                 (!FLGI
                  *CF* 1
                  (!FLGI *PF* 1
                         (!FLGI *AF* 1
                                (!FLGI *ZF* 1
                                       (!FLGI *SF* 0 (!FLGI *OF* 0 X86)))))))))))))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

                             select-segment-register

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-to-reg/mem$
                             wr64
                             wr32
                             rr32
                             rr64
                             rml32
                             rml64
                             wml32
                             wml64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             x86-operand-from-modr/m-and-sib-bytes$
                             check-instruction-length
                             address-aligned-p
                             riml-size
                             riml32
                             n32-to-i32
                             n64-to-i64
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             subset-p
                             signed-byte-p)
                            (mv-nth-1-wb-and-!flgi-commute
                             default-+-2
                             get-prefixes-opener-lemma-group-4-prefix
                             get-prefixes-opener-lemma-group-3-prefix
                             get-prefixes-opener-lemma-group-2-prefix
                             get-prefixes-opener-lemma-group-1-prefix)))))

(defthm effects-copyData-loop-base-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-base) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             mv-nth-1-wb-and-!flgi-commute
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies
   (and (loop-preconditions k m addr src-addr dst-addr x86)
        (<= m 4))
   (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
          (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-destination-address-projection-copied)
                        (:instance effects-copyData-loop-base-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k 4)
                                   (j k)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k 4)
                                   (j k)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k 4)
                                   (j k)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 x86)))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             rb-rb-split-reads
                             split-rb-in-app-view
                             loop-clk-base
                             effects-copyData-loop-base-destination-address-projection-copied
                             effects-copyData-loop-base-destination-address-projection-original
                             (loop-clk-base)
                             (:t xw)
                             canonical-address-p-limits-thm-0
                             default-+-1
                             default-+-2
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection-original
  ;; src[(+ -k src-addr) to src-addr] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes k src-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k src-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             mv-nth-1-wb-and-!flgi-commute
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection-copied
  ;; src[(src-addr) to (src-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes 4 (+ 4 src-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-source-address-projection
  ;; src[(+ -k src-addr) to (src-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (source-bytes (+ 4 k) (+ 4 src-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-source-address-projection-copied)
                        (:instance effects-copyData-loop-base-source-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-source-address-projection-copied
                             effects-copyData-loop-base-source-address-projection-original
                             rb-rb-split-reads
                             (loop-clk-base)
                             (:t xw)
                             canonical-address-p-limits-thm-0
                             default-+-1
                             default-+-2
                             force (force))))))

(defthm effects-copyData-loop-base-alignment-checking-enabled-p
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (alignment-checking-enabled-p (x86-run (loop-clk-base) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-app-view-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :app-view 0 (x86-run (loop-clk-base) x86))
                  (xr :app-view 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-base) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :fault 0 (x86-run (loop-clk-base) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :ms 0 (x86-run (loop-clk-base) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rip 0 (x86-run (loop-clk-base) x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r (x86-run (loop-clk-base) x86)))
                  (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-base)
                        (:instance loop-preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* ()
                            (loop-clk-base
                             loop-preconditions-fwd-chain-to-its-body
                             loop-preconditions
                             effects-copyData-loop-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (program-at addr *copyData* (x86-run (loop-clk-base) x86))
                  (program-at addr *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-64-bit-modep-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (equal prog-len (len *copydata*))
                (<= m 4))
           (equal (64-bit-modep (x86-run (loop-clk-base) x86))
                  (64-bit-modep x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

;; ======================================================================
