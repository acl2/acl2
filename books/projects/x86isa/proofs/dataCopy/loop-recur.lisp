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

(defthmd effects-copyData-loop-recur
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (x86-run (loop-clk-recur) x86)
                  (XW
                   :RGF *RAX*
                   (LOGHEAD 64
                            (+ 18446744073709551612
                               (XR :RGF *RAX* X86)))
                   (XW
                    :RGF *RCX*
                    (MV-NTH 1 (RB 4 (XR :RGF *RDI* X86) :R X86))
                    (XW
                     :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
                     (XW
                      :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
                      (XW
                       :RIP 0 (XR :RIP 0 X86)
                       (MV-NTH
                        1
                        (WB
                         4 (XR :RGF *RSI* X86)
                         :W
                         (MV-NTH 1 (RB 4 (XR :RGF *RDI* X86) :R X86))
                         (!FLGI
                          *CF*
                          (CF-SPEC64 (+ 18446744073709551612
                                        (XR :RGF *RAX* X86)))
                          (!FLGI
                           *PF*
                           (PF-SPEC64 (LOGHEAD 64
                                               (+ 18446744073709551612
                                                  (XR :RGF *RAX* X86))))
                           (!FLGI *AF*
                                  (ADD-AF-SPEC64 (XR :RGF *RAX* X86)
                                                 18446744073709551612)
                                  (!FLGI *ZF* 0
                                         (!FLGI *SF*
                                                (SF-SPEC64 (LOGHEAD 64
                                                                    (+ 18446744073709551612
                                                                       (XR :RGF *RAX* X86))))
                                                (!FLGI *OF*
                                                       (OF-SPEC64 (+ -4 (XR :RGF *RAX* X86)))
                                                       X86)))))))))))))))
  :hints (("Goal"
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
                            (get-prefixes-opener-lemma-group-4-prefix
                             get-prefixes-opener-lemma-group-3-prefix
                             get-prefixes-opener-lemma-group-2-prefix
                             get-prefixes-opener-lemma-group-1-prefix)))))

(defthm effects-copyData-loop-recur-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-recur) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-recur)
                 (:instance effects-copyData-loop-recur-destination-address-projection-copied)
                 (:instance effects-copyData-loop-recur-destination-address-projection-original)
                 (:instance rb-rb-split-reads
                            (k 4)
                            (j k)
                            (r-x :r)
                            (addr (+ (- k) (xr :rgf *rsi* x86)))
                            (x86 (x86-run (loop-clk-recur) x86)))
                 (:instance rb-rb-split-reads
                            (k 4)
                            (j k)
                            (r-x :r)
                            (addr (+ (- k) (xr :rgf *rdi* x86)))
                            (x86 x86)))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-original
  ;; src[(+ -k src-addr) to src-addr] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes k src-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k src-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-copied
  ;; src[(src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes 4 (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection
  ;; src[(+ -k src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ 4 k) (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-source-address-projection-copied)
                        (:instance effects-copyData-loop-recur-source-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k 4)
                                   (j k)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86)))
                        (:instance rb-rb-split-reads
                                   (k 4)
                                   (j k)
                                   (r-x :r)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 x86)))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-app-view-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :app-view 0 (x86-run (loop-clk-recur) x86))
                  (xr :app-view 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-alignment-checking-enabled-p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (alignment-checking-enabled-p (x86-run (loop-clk-recur) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :ms 0 (x86-run (loop-clk-recur) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :fault 0 (x86-run (loop-clk-recur) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m)
                (equal prog-len (len *copydata*)))
           (equal (program-at addr *copyData* (x86-run (loop-clk-recur) x86))
                  (program-at addr *copyData* x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-recur) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rax-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rax* (x86-run (loop-clk-recur) x86))
                  (loghead 64 (+ #xfffffffffffffffc (xr :rgf *rax* x86)))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rip 0 (x86-run (loop-clk-recur) x86))
                  (xr :rip 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-x86p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (x86p (x86-run (loop-clk-recur) x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (separate-smaller-regions
                                    loop-clk-recur
                                    (loop-clk-recur)
                                    force (force))))))

(defthm effects-copyData-loop-recur-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r (x86-run (loop-clk-recur) x86)))
                  (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur)
                        (:instance loop-preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             loop-preconditions-fwd-chain-to-its-body
                             loop-preconditions
                             effects-copyData-loop-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-64-bit-modep-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (64-bit-modep (x86-run (loop-clk-recur) x86))
                  (64-bit-modep x86)))
  :hints (("Goal"
           :use effects-copyData-loop-recur
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-implies-loop-preconditions
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (loop-preconditions (+ 4 k)
                               (loghead 64 (+ #xfffffffffffffffc m))
                               addr (+ 4 src-addr)
                               (+ 4 dst-addr)
                               (x86-run (loop-clk-recur) x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance loop-preconditions-fwd-chain-to-its-body))
           :expand (loop-preconditions (+ 4 k)
                                       (+ -4 (xr :rgf *rax* x86))
                                       (+ -16 (xr :rip 0 x86))
                                       (+ 4 (xr :rgf *rdi* x86))
                                       (+ 4 (xr :rgf *rsi* x86))
                                       (x86-run (loop-clk-recur) x86))
           :in-theory (e/d* (unsigned-byte-p
                             effects-copyData-loop-helper-11
                             effects-copyData-loop-helper-14)
                            (loop-clk-recur
                             rb-rb-split-reads
                             destination-bytes
                             source-bytes
                             loop-preconditions
                             loop-preconditions-fwd-chain-to-its-body
                             (loop-clk-recur)
                             force (force))))))

;; ======================================================================
