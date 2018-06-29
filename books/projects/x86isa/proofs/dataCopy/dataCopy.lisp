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
(include-book "loop-base" :ttags :all)
(include-book "loop-recur" :ttags :all)
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

(defun-nx loop-state (k m src-addr dst-addr x86)

  (if (signed-byte-p 64 m) ;; This should always be true.

      (if (<= m 4)

          (x86-run (loop-clk-base) x86)

        (b* ((new-m (loghead 64 (+ #xfffffffffffffffc m)))
             (new-k (+ 4 k))
             (new-src-addr (+ 4 src-addr))
             (new-dst-addr (+ 4 dst-addr))
             (x86 (x86-run (loop-clk-recur) x86)))
          (loop-state new-k new-m new-src-addr new-dst-addr x86)))
    x86))

(defthmd x86-run-plus-for-loop-clk-recur-1
  (equal (x86-run (loop-clk (loghead 64 (+ #xfffffffffffffffc m)))
                  (x86-run (loop-clk-recur) x86))
         (x86-run (binary-clk+ (loop-clk-recur)
                               (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                  x86))
  :hints (("Goal" :in-theory (e/d* () (x86-run-plus (loop-clk-recur) loop-clk-recur))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                            (n1 (loop-clk-recur)))))))

(defthm effects-copyData-loop
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (equal (x86-run (loop-clk m) x86)
                  (loop-state k m src-addr dst-addr x86)))
  :hints (("Goal"
           :induct (cons (loop-state k m src-addr dst-addr x86) (loop-clk m))
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

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
                             riml-size
                             riml32
                             n32-to-i32
                             n64-to-i64
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             signed-byte-p

                             x86-run-plus-for-loop-clk-recur-1)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             ;; [Shilpi]: Note that the executable-counterpart
                             ;; of loop-clk needs to be disabled, else
                             ;; (loop-clk-base) will be rewritten to 6,
                             ;; irrespective of whether loop-clk-base is
                             ;; completely disabled.
                             (loop-clk)
                             loop-preconditions
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-full-helper
  ;; src[src-addr to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[src-addr to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes m (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-full
  ;; src[(+ -k src-addr) to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ m k) (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ m k) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-recur)
                 (:instance effects-copyData-loop-recur-source-address-projection-copied)
                 (:instance effects-copyData-loop-recur-source-address-projection-original)
                 (:instance effects-copyData-loop-recur-source-address-projection-full-helper)
                 (:instance rb-rb-split-reads
                            (k k)
                            (j m)
                            (r-x :r)
                            (addr (+ (- k) (xr :rgf *rdi* x86)))
                            (x86 (x86-run (loop-clk-recur) x86)))
                 (:instance rb-rb-split-reads
                            (k k)
                            (j (xr :rgf *rax* x86))
                            (r-x :r)
                            (addr (+ (- k) (xr :rgf *rdi* x86)))
                            (x86 x86)))
           :in-theory (e/d* ()
                            (separate-smaller-regions
                             rb-rb-split-reads
                             (:t xw)
                             default-+-1
                             default-+-2
                             loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-full-helper
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             (loop-clk-recur)
                             (:type-prescription natp-of-mv-nth-1-rb)
                             force (force))))))

(local
 (defthmd source-array-and-loop-state-helper
   (implies
    (and
     (< 4 m)
     (equal (source-bytes (+ 4 k
                             (loghead 64 (+ 18446744073709551612 m)))
                          (+ 4 src-addr
                             (loghead 64 (+ 18446744073709551612 m)))
                          (loop-state (+ 4 k)
                                      (loghead 64 (+ 18446744073709551612 m))
                                      (+ 4 src-addr)
                                      (+ 4 dst-addr)
                                      (x86-run (loop-clk-recur) x86)))
            (source-bytes (+ 4 k
                             (loghead 64 (+ 18446744073709551612 m)))
                          (+ 4 src-addr
                             (loghead 64 (+ 18446744073709551612 m)))
                          (x86-run (loop-clk-recur) x86)))
     (loop-preconditions k m addr src-addr dst-addr x86))
    (equal (source-bytes (+ k m)
                         (+ m src-addr)
                         (loop-state (+ 4 k)
                                     (loghead 64 (+ 18446744073709551612 m))
                                     (+ 4 src-addr)
                                     (+ 4 dst-addr)
                                     (x86-run (loop-clk-recur) x86)))
           (source-bytes (+ k m)
                         (+ m src-addr)
                         x86)))
   :hints (("Goal"
            :use ((:instance effects-copyData-loop-recur-source-address-projection-full))
            :hands-off (x86-run)
            :in-theory (e/d* (effects-copyData-loop-helper-11)
                             (loop-preconditions
                              effects-copyData-loop-recur-source-address-projection-full
                              loop-invariant
                              destination-bytes
                              source-bytes
                              loop-clk-recur
                              (loop-clk-recur)
                              loop-clk-base
                              (loop-clk-base)))))))

(defthmd source-array-and-loop-state
  ;; src[(+ -k src-addr) to (src-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (source-bytes (+ k m) (+ m src-addr) (loop-state k m src-addr dst-addr x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* (source-array-and-loop-state-helper)
                            (loop-preconditions
                             loop-invariant
                             source-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthmd source-array-and-x86-state-after-loop-clk
  ;; src[(+ -k src-addr) to (src-addr + m)] in (loop-state k m src-addr src-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (source-bytes (+ k m) (+ m src-addr) (x86-run (loop-clk m) x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop)
                 (:instance source-array-and-loop-state))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (effects-copyData-loop
                             loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             loop-clk
                             (loop-clk))))))

(defthm loop-leaves-m-bytes-of-source-unmodified
  ;; src[ src-addr to (src-addr + m) ] in (loop-state 0 m src-addr src-addr x86) =
  ;; src[ src-addr to (src-addr + m) ] in x86
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (source-bytes m (+ m src-addr) (x86-run (loop-clk m) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance source-array-and-x86-state-after-loop-clk
                            (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             destination-bytes
                             source-bytes
                             (loop-clk-base)
                             loop-preconditions
                             effects-copyData-loop
                             effects-copyData-loop-base
                             effects-copyData-loop-recur
                             force (force))))))

(defthmd destination-array-and-loop-state
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (loop-state k m src-addr dst-addr x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))
          ;; Ugh, banish this subgoal hint!
          ("Subgoal *1/3"
           :use
           ((:instance effects-copyData-loop-recur-source-address-projection-full))
           :hands-off (x86-run)
           :in-theory (e/d* (effects-copyData-loop-helper-11)
                            (loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthmd destination-array-and-x86-state-after-loop-clk
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop)
                 (:instance destination-array-and-loop-state))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (effects-copyData-loop
                             loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             loop-clk
                             (loop-clk))))))

(defthm loop-copies-m-bytes-from-source-to-destination
  ;; dst[ dst-addr to (dst-addr + m) ] in (loop-state 0 m src-addr dst-addr x86) =
  ;; src[ src-addr to (src-addr + m) ] in x86
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (destination-bytes m (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance destination-array-and-x86-state-after-loop-clk
                            (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-clk-recur
                             destination-array-and-loop-state
                             (loop-clk-recur)
                             loop-clk-base
                             destination-bytes
                             source-bytes
                             (loop-clk-base)
                             loop-preconditions
                             effects-copyData-loop
                             effects-copyData-loop-base
                             effects-copyData-loop-recur
                             force (force))))))

;; ======================================================================

(defun-nx preconditions (n addr x86)
  (and (x86p x86)
       (64-bit-modep x86)
       (xr :app-view 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the copyData sub-routine.
       (equal (xr :rip 0 x86) addr)
       ;; [Shilpi] This used to be (unsigned-byte-p 32 n), but I
       ;; needed to make this change after fixing the NOP/XCHG bug.
       (unsigned-byte-p 14 n) ;; 32?
       (equal (xr :rgf *rdx* x86) n)
       ;; All the stack addresses are canonical.
       (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       ;; Return address of the copyData sub-routine is canonical.
       (canonical-address-p
        (logext 64 (mv-nth 1 (rb  8 (xr :rgf *rsp* x86) :r x86))))
       ;; All the destination addresses are canonical.
       (canonical-address-p (xr :rgf *rsi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (xr :rgf *rdi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           ;; rsi and rdi point to doublewords (four bytes), so their
           ;; natural boundary will be addresses divisible by 4.
           (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                (equal (loghead 2 (xr :rgf *rdi* x86)) 0)
                ;; rsp will be aligned to a 16-byte boundary.
                (equal (loghead 3 (+ -8 (xr :rgf *rsp* x86))) 0))
         t)
       ;; Memory locations of interest are disjoint.
       (separate
        ;; Location of the Return Address (on the stack)
        :r 8 (xr :rgf *rsp* x86)
        ;; Destination Addresses
        :w (ash n 2) (xr :rgf *rsi* x86))
       (separate
        ;; Program addresses
        :x *prog-len* addr
        ;; Destination addresses
        :w (ash n 2) (xr :rgf *rsi* x86))
       (separate ;; Read from stack
        ;; Program addresses
        :x *prog-len* addr
        ;; Stack
        :r 16 (+ -8 (xr :rgf *rsp* x86)))
       (separate ;; Write to stack
        ;; Program addresses
        :x *prog-len* addr
        ;; Stack
        :w 16 (+ -8 (xr :rgf *rsp* x86)))
       (separate ;; Read from stack
        ;; Source Addresses
        :r (ash n 2) (xr :rgf *rdi* x86)
        ;; Stack
        :r 16 (+ -8 (xr :rgf *rsp* x86)))
       (separate ;; Write to stack
        ;; Source Addresses
        :r (ash n 2) (xr :rgf *rdi* x86)
        ;; Stack
        :w 16 (+ -8 (xr :rgf *rsp* x86)))
       (separate
        ;; Destination Addresses
        :w (ash n 2) (xr :rgf *rsi* x86)
        ;; Stack
        :r 16 (+ -8 (xr :rgf *rsp* x86)))
       (separate
        ;; Source Addresses
        :r (ash n 2) (xr :rgf *rdi* x86)
        ;; Destination Addresses
        :w (ash n 2) (xr :rgf *rsi* x86))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ *prog-len* addr))
       (program-at addr *copyData* x86)))

(defthm preconditions-fwd-chain-to-its-body
  (implies (preconditions n addr x86)
           (and (x86p x86)
                (64-bit-modep x86)
                (xr :app-view 0 x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; We are poised to run the copyData sub-routine.
                (equal (xr :rip 0 x86) addr)
                (unsigned-byte-p 32 n)
                (equal (xr :rgf *rdx* x86) n)
                ;; All the stack addresses are canonical.
                (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                ;; Return address of the copyData sub-routine is canonical.
                (canonical-address-p
                 (logext 64 (mv-nth 1 (rb  8 (xr :rgf *rsp* x86) :r x86))))
                ;; All the destination addresses are canonical.
                (canonical-address-p (xr :rgf *rsi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (xr :rgf *rdi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
                ;; Alignment Checking
                (if (alignment-checking-enabled-p x86)
                    ;; rsi and rdi point to doublewords (four bytes), so their
                    ;; natural boundary will be addresses divisible by 4.
                    (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                         (equal (loghead 2 (xr :rgf *rdi* x86)) 0)
                         ;; rsp will be aligned to a 16-byte boundary.
                         (equal (loghead 3 (+ -8 (xr :rgf *rsp* x86))) 0))
                  t)
                ;; Memory locations of interest are disjoint.
                (separate
                 ;; Location of the Return Address (on the stack)
                 :r 8 (xr :rgf *rsp* x86)
                 ;; Destination Addresses
                 :w (ash n 2) (xr :rgf *rsi* x86))
                (separate
                 ;; Program addresses
                 :x *prog-len* addr
                 ;; Destination addresses
                 :w (ash n 2) (xr :rgf *rsi* x86))
                (separate ;; Read from stack
                 ;; Program addresses
                 :x *prog-len* addr
                 ;; Stack
                 :r 16 (+ -8 (xr :rgf *rsp* x86)))
                (separate ;; Write to stack
                 ;; Program addresses
                 :x *prog-len* addr
                 ;; Stack
                 :w 16 (+ -8 (xr :rgf *rsp* x86)))
                (separate ;; Read from stack
                 ;; Source Addresses
                 :r (ash n 2) (xr :rgf *rdi* x86)
                 ;; Stack
                 :r 16 (+ -8 (xr :rgf *rsp* x86)))
                (separate ;; Write to stack
                 ;; Source Addresses
                 :r (ash n 2) (xr :rgf *rdi* x86)
                 ;; Stack
                 :w 16 (+ -8 (xr :rgf *rsp* x86)))
                (separate
                 ;; Destination Addresses
                 :w (ash n 2) (xr :rgf *rsi* x86)
                 ;; Stack
                 :r 16 (+ -8 (xr :rgf *rsp* x86)))
                (separate
                 ;; Source Addresses
                 :r (ash n 2) (xr :rgf *rdi* x86)
                 ;; Destination Addresses
                 :w (ash n 2) (xr :rgf *rsi* x86))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ *prog-len* addr))
                (program-at addr *copyData* x86)))
  :rule-classes :forward-chaining)

(local
 (defthm rdx-logsquash-lemma
   (implies (unsigned-byte-p 14 rdx)
            (equal (logext 64 (bitops::logsquash 16 (ash rdx 2)))
                   0))
   :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                     bitops::ihsext-inductions
                                     unsigned-byte-p)
                                    ())))))

(defthm effects-copyData-pre
  (implies
   (preconditions n addr x86)
   (equal
    (x86-run (pre-clk n) x86)
    (if (< 0 n)
        (XW
         :RGF *RAX* (LOGHEAD 16 (ASH (XR :RGF *RDX* X86) 2))
         (XW
          :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
          (XW
           :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
           (XW
            :RIP 0 (+ 16 (XR :RIP 0 X86))
            (MV-NTH
             1
             (WB
              8 (+ -8 (XR :RGF *RSP* X86))
              :W (LOGHEAD 64 (XR :RGF *RBP* X86))
              (WRITE-USER-RFLAGS
               (LOGIOR
                (LOGHEAD 32
                         (ASH (PF-SPEC64 (ASH (XR :RGF *RDX* X86) 2))
                              2))
                (LOGAND
                 4294967226
                 (LOGIOR
                  (LOGHEAD 32
                           (ASH (SF-SPEC64 (ASH (XR :RGF *RDX* X86) 2))
                                7))
                  (LOGAND
                   4294967166
                   (BITOPS::LOGSQUASH
                    1
                    (XR
                     :RFLAGS 0
                     (WRITE-USER-RFLAGS
                      (LOGIOR
                       (LOGHEAD 32
                                (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                       (LOGAND
                        4294967226
                        (LOGIOR (LOGAND 4294965118
                                        (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                (LOGHEAD 32
                                         (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                              7)))))
                      16 X86)))))))
               2064
               (WRITE-USER-RFLAGS
                (LOGIOR
                 (LOGHEAD 32
                          (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                 (LOGAND 4294967226
                         (LOGIOR (LOGAND 4294965118
                                         (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                 (LOGHEAD 32
                                          (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                               7)))))
                16 X86))))))))
      (XW
       :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
       (XW
        :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
        (XW
         :RIP 0 (+ 34 (XR :RIP 0 X86))
         (MV-NTH
          1
          (WB
           8 (+ -8 (XR :RGF *RSP* X86))
           :W (LOGHEAD 64 (XR :RGF *RBP* X86))
           (WRITE-USER-RFLAGS
            (LOGIOR
             4
             (LOGAND 4294967290
                     (LOGIOR 64
                             (LOGAND 4294965054
                                     (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86))))))
            16 X86)))))))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec
                                    sal/shl-spec-64
                                    address-aligned-p

                                    top-level-opcode-execute
                                    !rgfi-size
                                    x86-operand-to-reg/mem
                                    x86-operand-to-reg/mem$
                                    wr64
                                    wr32
                                    wr16
                                    rr16
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
                                    riml-size
                                    riml32
                                    n32-to-i32
                                    n64-to-i64
                                    riml08
                                    two-byte-opcode-decode-and-execute
                                    x86-effective-addr)
                                   (not force (force))))))

(defthm effects-copyData-pre-app-view-projection
  (implies (preconditions n addr x86)
           (equal (xr :app-view 0 (x86-run (pre-clk n) x86))
                  (xr :app-view 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rsi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rdi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rdi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rdi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsp-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsp* (x86-run (pre-clk n) x86))
                  (+ -8 (xr :rgf *rsp* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rax-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rgf *rax* (x86-run (pre-clk n) x86))
                  (ash n 2)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-program-at-projection
  (implies (and (preconditions n addr x86)
                (equal prog-len *prog-len*))
           (equal (program-at addr *copyData* (x86-run (pre-clk n) x86))
                  (program-at addr *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-fault-projection
  (implies (preconditions n addr x86)
           (equal (xr :fault 0 (x86-run (pre-clk n) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-ms-projection
  (implies (preconditions n addr x86)
           (equal (xr :ms 0 (x86-run (pre-clk n) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rip-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rip 0 (x86-run (pre-clk n) x86))
                  (+ 16 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-x86p-projection
  (implies (preconditions n addr x86)
           (x86p (x86-run (pre-clk n) x86)))
  :hints (("Goal" :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-return-address-projection
  (implies (preconditions n addr x86)
           (equal (mv-nth 1 (rb 8 (xr :rgf *rsp* x86) :r (x86-run (pre-clk n) x86)))
                  (mv-nth 1 (rb 8 (xr :rgf *rsp* x86) :r x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* (canonical-address-p-limits-thm-3)
                            ((pre-clk) pre-clk force (force)
                             preconditions)))))

(defthm effects-copyData-pre-alignment-checking-enabled-p-projection
  (implies (preconditions n addr x86)
           (equal (alignment-checking-enabled-p (x86-run (pre-clk n) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre))
           :in-theory (e/d* (alignment-checking-enabled-p)
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-64-bit-modep-projection
  (implies (preconditions n addr x86)
           (equal (64-bit-modep (x86-run (pre-clk n) x86))
                  (64-bit-modep x86)))
  :hints (("Goal"
           :use effects-copyData-pre
           :in-theory (e/d* (64-bit-modep)
                            (pre-clk (pre-clk)
                             force (force))))))

(defthm preconditions-implies-loop-preconditions-after-pre-clk
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (loop-preconditions
            0 m addr
            (xr :rgf *rdi* x86) ;; src-addr
            (xr :rgf *rsi* x86) ;; dst-addr
            (x86-run (pre-clk n) x86)))
  :hints (("Goal" :hands-off (x86-run)
           :use ((:instance preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* (unsigned-byte-p
                             canonical-address-p-limits-thm-3)
                            (pre-clk
                             (pre-clk) preconditions
                             preconditions-fwd-chain-to-its-body)))))

(defthmd x86-run-plus-for-clk
  (equal (x86-run (binary-clk+ (pre-clk n) (loop-clk (ash n 2))) x86)
         (x86-run (loop-clk (ash n 2)) (x86-run (pre-clk n) x86)))
  :hints (("Goal" :in-theory (e/d* (binary-clk+)
                                   (x86-run-plus
                                    (loop-clk)
                                    loop-clk
                                    pre-clk
                                    (pre-clk)))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk (ash n 2)))
                            (n1 (pre-clk n)))))))

(defthmd pre+loop-copies-m-bytes-from-source-to-destination-helper-1
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal
            (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (clk n) x86))
            (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (pre-clk n) x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (effects-copydata-loop
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-preconditions
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             force (force))))))

(defthmd pre+loop-copies-m-bytes-from-source-to-destination-helper-2
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal
            (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (pre-clk n) x86))
            (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-pre))
           :in-theory (e/d* (preconditions)
                            (effects-copyData-pre
                             preconditions-implies-loop-preconditions-after-pre-clk
                             destination-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             force (force))))))

(defthm pre+loop-copies-m-bytes-from-source-to-destination
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal
            (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (clk n) x86))
            (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-1)
                 (:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-2))
           :in-theory (e/d* ()
                            (preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             clk
                             (pre-clk)
                             force (force))))))

(defthm pre+loop-leaves-m-bytes-of-source-unmodified
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk)
                 (:instance pre+loop-copies-m-bytes-from-source-to-destination-helper-2))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             effects-copydata-loop
                             preconditions
                             destination-bytes
                             source-bytes
                             (loop-clk)
                             loop-clk
                             pre-clk
                             (pre-clk)
                             force (force))))))

;; Now, to prove a theorem similar to
;; pre+loop-copies-m-bytes-from-source-to-destination, but in terms of
;; program-clk...

(defthm loop-state-app-view-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :app-view 0 (loop-state k m src-addr dst-addr x86))
                  (xr :app-view 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm loop-clk-app-view-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :app-view 0 (x86-run (loop-clk m) x86))
                  (xr :app-view 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k)
                (equal prog-len *prog-len*))
           (equal (program-at addr *copyData* (loop-state k m src-addr dst-addr x86))
                  (program-at addr *copyData* x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-program-at-projection
  (implies (and (loop-preconditions 0 m addr src-addr dst-addr x86)
                (equal prog-len *prog-len*))
           (equal (program-at addr *copyData* (x86-run (loop-clk m) x86))
                  (program-at addr *copyData* x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :ms 0 (loop-state k m src-addr dst-addr x86))
                  (xr :ms 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-ms-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :ms 0 (x86-run (loop-clk m) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :fault 0 (loop-state k m src-addr dst-addr x86))
                  (xr :fault 0 x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-fault-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :fault 0 (x86-run (loop-clk m) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rip 0 (loop-state k m src-addr dst-addr x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-rip-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rip 0 (x86-run (loop-clk m) x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rsp* (loop-state k m src-addr dst-addr x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-rsp-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rsp* (x86-run (loop-clk m) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rsi* (loop-state k m src-addr dst-addr x86))
                  (+ m dst-addr)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))
          ;; Ugh, another one of these subgoal hints...
          ("Subgoal *1/3" :in-theory (e/d* (effects-copyData-loop-helper-11)
                                           (loop-preconditions)))))

(defthm loop-clk-rsi-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rsi* (x86-run (loop-clk m) x86))
                  (+ m dst-addr)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm clk-rsi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsi* (x86-run (clk n) x86))
                  (+ (ash n 2) (xr :rgf *rsi* x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk
                            (m (ash n 2))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions
                             (loop-clk) loop-clk (pre-clk)
                             (clk)
                             pre-clk
                             effects-copydata-loop
                             effects-copydata-pre)))))

(defthm loop-state-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (xr :rgf *rdi* (loop-state k m src-addr dst-addr x86))
                  (+ m src-addr)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))
          ("Subgoal *1/3" :in-theory (e/d* (effects-copyData-loop-helper-11)
                                           (loop-preconditions)))))

(defthm loop-clk-rdi-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (xr :rgf *rdi* (x86-run (loop-clk m) x86))
                  (+ m src-addr)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm clk-rdi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rdi* (x86-run (clk n) x86))
                  (+ (ash n 2) (xr :rgf *rdi* x86))))
  :hints (("Goal"
           :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk
                            (m (ash n 2))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            (loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions
                             (loop-clk) loop-clk (pre-clk)
                             (clk)
                             pre-clk
                             effects-copydata-loop
                             effects-copydata-pre)))))

(defthm loop-state-return-address-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal
            (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86))
                          :r (loop-state k m src-addr dst-addr x86)))
            (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-return-address-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (mv-nth 1
                          (rb 8 (+ 8 (xr :rgf *rsp* x86))
                              :r (x86-run (loop-clk m) x86)))
                  (mv-nth 1
                          (rb 8 (+ 8 (xr :rgf *rsp* x86))
                              :r x86))))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-alignment-checking-enabled-p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (alignment-checking-enabled-p (loop-state k m src-addr dst-addr x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base))))))

(defthm loop-clk-alignment-checking-enabled-p-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (alignment-checking-enabled-p (x86-run (loop-clk m) x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop)))))

(defthm loop-state-64-bit-modep-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (64-bit-modep (loop-state k m src-addr dst-addr x86))
                  (64-bit-modep x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm loop-clk-64-bit-modep-projection
  (implies (loop-preconditions 0 m addr src-addr dst-addr x86)
           (equal (64-bit-modep (x86-run (loop-clk m) x86))
                  (64-bit-modep x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             (loop-clk) loop-clk
                             effects-copydata-loop
                             create-canonical-address-list)))))

(defun-nx after-the-copy-conditions (n addr x86)
  (and (x86p x86)
       (64-bit-modep x86)
       (xr :app-view 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the last two instructions.
       (equal addr (+ -34 (xr :rip 0 x86)))
       ;; All the stack addresses are canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       (canonical-address-p (+ 16 (xr :rgf *rsp* x86)))
       ;; The value of the return address is canonical.
       (canonical-address-p
        (logext 64 (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           (equal (loghead 3 (xr :rgf *rsp* x86)) 0)
         t)
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       ;; [Shilpi]: Why not (canonical-address-p (+ -1 *prog-len* addr))?
       ;; In case of instructions like ret and jump, hyp 20 of
       ;; x86-fetch-decode-execute-opener doesn't apply. Modify?
       ;; (CANONICAL-ADDRESS-P$INLINE (BINARY-+ '2 (XR ':RIP '0 X86)))
       (canonical-address-p (+ *prog-len* addr))
       (program-at addr *copyData* x86)))

(defthmd preconditions-implies-after-the-copy-conditions-after-clk-helper
  (implies (and (loop-preconditions 0 (ash n 2)
                                    addr (xr :rgf *rdi* x86)
                                    (xr :rgf *rsi* x86)
                                    (x86-run (pre-clk n) x86))
                (preconditions n addr x86))
           (canonical-address-p
            (logext
             64
             (mv-nth
              1
              (rb 8 (+ 8 (xr :rgf *rsp* (x86-run (pre-clk n) x86)))
                  :r (x86-run (loop-clk (ash n 2)) (x86-run (pre-clk n) x86)))))))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            ((loop-clk)
                             loop-clk
                             (pre-clk)
                             pre-clk
                             effects-copyData-loop
                             effects-copyData-pre-rsp-projection
                             preconditions
                             loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             effects-copydata-pre)))))

(defthm preconditions-implies-after-the-copy-conditions-after-clk
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (after-the-copy-conditions n addr (x86-run (clk n) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-fwd-chain-to-its-body)
                 (:instance preconditions-implies-after-the-copy-conditions-after-clk-helper)
                 (:instance effects-copyData-pre-rsp-projection)
                 (:instance preconditions-implies-loop-preconditions-after-pre-clk
                            (m (ash n 2)))
                 (:instance effects-copyData-loop
                            (k 0) (src-addr (xr :rgf *rdi* x86))
                            (dst-addr (xr :rgf *rsi* x86))))
           :in-theory (e/d* (x86-run-plus-for-clk)
                            ((loop-clk)
                             loop-clk
                             (pre-clk)
                             pre-clk
                             effects-copyData-loop
                             effects-copyData-pre-rsp-projection
                             preconditions
                             loop-preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             effects-copydata-pre)))))

(defthmd effects-copyData-after-clk
  (implies (after-the-copy-conditions n addr x86)
           (equal
            (x86-run (post-clk) x86)
            (XW :RGF *RSP* (+ 16 (XR :RGF *RSP* X86))
                (XW :RGF *RBP*
                    (LOGEXT 64
                            (MV-NTH 1 (RB 8 (XR :RGF *RSP* X86) :R X86)))
                    (XW :RIP 0
                        (LOGEXT 64
                                (MV-NTH 1
                                        (RB 8 (+ 8 (XR :RGF *RSP* X86))
                                            :R X86)))
                        X86)))))
  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             64-bit-modep
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
                             riml-size
                             riml32
                             riml64
                             n32-to-i32
                             n64-to-i64
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             address-aligned-p
                             signed-byte-p)
                            ()))))

(defthmd x86-run-plus-for-program-clk
  (equal (x86-run (binary-clk+ (clk n) (post-clk)) x86)
         (x86-run (post-clk) (x86-run (clk n) x86)))
  :hints (("Goal" :in-theory (e/d* (binary-clk+)
                                   (x86-run-plus
                                    (loop-clk)
                                    loop-clk
                                    pre-clk
                                    (pre-clk)))
           :use ((:instance x86-run-plus
                            (n1 (clk n))
                            (n2 (post-clk)))))))

(defthmd program-copies-m-bytes-from-source-to-destination-till-finish-helper-1
  ;; (xr :rgf *rsi* x86) here is really (+ m (xr :rgf *rsi* x86_0)), where
  ;; x86_0 is the state before the loop.
  (implies (and (after-the-copy-conditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (destination-bytes m (xr :rgf *rsi* x86) (x86-run (post-clk) x86))
                  (destination-bytes m (xr :rgf *rsi* x86) x86)))
  :hints (("Goal" :use ((:instance effects-copyData-after-clk))
           :in-theory (e/d* ()
                            (preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

(defthm program-copies-m-bytes-from-source-to-destination-till-finish-helper-2
  (implies
   (and (preconditions n addr x86)
        (not (zp n))
        (equal m (ash n 2)))
   (equal
    (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (program-clk n) x86))
    (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-after-the-copy-conditions-after-clk)
                 (:instance program-copies-m-bytes-from-source-to-destination-till-finish-helper-1
                            (x86 (x86-run (clk n) x86))))
           :in-theory (e/d* (x86-run-plus-for-program-clk)
                            (after-the-copy-conditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions-implies-after-the-copy-conditions-after-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

(defthmd program-leaves-m-bytes-of-source-unmodified-helper-1
  ;; (xr :rgf *rsi* x86) here is really (+ m (xr :rgf *rsi* x86_0)), where
  ;; x86_0 is the state before the loop.
  (implies (and (after-the-copy-conditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (xr :rgf *rdi* x86) (x86-run (post-clk) x86))
                  (source-bytes m (xr :rgf *rdi* x86) x86)))
  :hints (("Goal" :use ((:instance effects-copyData-after-clk))
           :in-theory (e/d* ()
                            (preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

(defthmd program-leaves-m-bytes-of-source-unmodified-helper-2
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (equal (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (program-clk n) x86))
                  (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-after-the-copy-conditions-after-clk)
                 (:instance program-leaves-m-bytes-of-source-unmodified-helper-1
                            (x86 (x86-run (clk n) x86))))
           :in-theory (e/d* (x86-run-plus-for-program-clk)
                            (after-the-copy-conditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions-implies-after-the-copy-conditions-after-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

(defthm destination-array-is-a-copy-of-the-source-array
  (implies
   (and (preconditions n addr x86)
        (equal m (ash n 2)))
   (equal
    (destination-bytes m (+ m (xr :rgf *rsi* x86)) (x86-run (program-clk n) x86))
    (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal"
           :use ((:instance program-copies-m-bytes-from-source-to-destination-till-finish-helper-2))
           :in-theory (e/d* ()
                            (program-copies-m-bytes-from-source-to-destination-till-finish-helper-2
                             after-the-copy-conditions
                             preconditions
                             clk post-clk pre-clk
                             (clk) (post-clk) (pre-clk)
                             force (force))))))

(defthm source-array-is-unmodified
  (implies (and (preconditions n addr x86)
                (equal m (ash n 2)))
           (equal
            (source-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (program-clk n) x86))
            (source-bytes m (+ m (xr :rgf *rdi* x86)) x86)))
  :hints (("Goal" :use ((:instance program-leaves-m-bytes-of-source-unmodified-helper-2))
           :in-theory (e/d* ()
                            (after-the-copy-conditions
                             preconditions
                             clk post-clk pre-clk
                             (clk) (post-clk) (pre-clk)
                             force (force))))))

(defthmd preconditions-implies-after-the-copy-conditions-after-clk-n=0
  (implies (preconditions 0 addr x86)
           (after-the-copy-conditions 0 addr (x86-run (clk 0) x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre (n 0)))
           :hands-off (x86-run)
           :in-theory (e/d* (x86-run-plus-for-clk
                             loop-preconditions)
                            (effects-copydata-pre
                             (pre-clk)
                             pre-clk
                             (clk)
                             preconditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             effects-copydata-pre)))))

(defthmd no-error-during-program-execution-helper
  (implies (after-the-copy-conditions n addr x86)
           (and (equal (ms (x86-run (post-clk) x86)) nil)
                (equal (fault (x86-run (post-clk) x86)) nil)))
  :hints (("Goal" :use ((:instance effects-copyData-after-clk))
           :in-theory (e/d* ()
                            (preconditions-implies-loop-preconditions-after-pre-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

(defthm no-error-during-program-execution
  (implies (preconditions n addr x86)
           (and (equal (ms (x86-run (program-clk n) x86)) nil)
                (equal (fault (x86-run (program-clk n) x86)) nil)))
  :hints (("Goal"
           :use ((:instance preconditions-implies-after-the-copy-conditions-after-clk)
                 (:instance no-error-during-program-execution-helper
                            (x86 (x86-run (clk n) x86))))
           :in-theory (e/d* (x86-run-plus-for-program-clk
                             preconditions-implies-after-the-copy-conditions-after-clk-n=0)
                            (after-the-copy-conditions
                             preconditions-implies-loop-preconditions-after-pre-clk
                             preconditions-implies-after-the-copy-conditions-after-clk
                             loop-copies-m-bytes-from-source-to-destination
                             effects-copydata-pre
                             preconditions
                             destination-bytes
                             source-bytes
                             clk post-clk
                             (clk) (post-clk)
                             force (force))))))

;; ======================================================================

;; Now, the top-level theorem:

(defun-nx source (n src-addr x86)
  (source-bytes (ash n 2) (+ (ash n 2) src-addr) x86))

(defun-nx destination (n dst-addr x86)
  (destination-bytes (ash n 2) (+ (ash n 2) dst-addr) x86))

(defun-nx copyData-preconditions (n src-addr dst-addr prog-addr x86)
  (and
   (equal (xr :rgf *rdi* x86) src-addr)
   (equal (xr :rgf *rsi* x86) dst-addr)
   (preconditions n prog-addr x86)))

(defthm copyData-is-correct
  (implies
   (copyData-preconditions n src-addr dst-addr prog-addr x86)
   (and
    ;; Destination location after program's execution contains
    ;; the same data as the source location before program's
    ;; execution.
    (equal (destination n dst-addr (x86-run (program-clk n) x86))
           (source n src-addr x86))
    ;; Source location after program's execution contains the
    ;; same data as it did before program's execution.
    (equal (source n src-addr (x86-run (program-clk n) x86))
           (source n src-addr x86))
    ;; No error was encountered during program's execution.
    (equal (ms (x86-run (program-clk n) x86)) nil)
    (equal (fault (x86-run (program-clk n) x86)) nil)))
  :hints (("Goal"
           :use ((:instance source-array-is-unmodified
                            (addr prog-addr)
                            (m (ash n 2)))
                 (:instance destination-array-is-a-copy-of-the-source-array
                            (addr prog-addr)
                            (m (ash n 2)))
                 (:instance no-error-during-program-execution
                            (addr prog-addr)))
           :in-theory (e/d* ()
                            (source-array-is-unmodified
                             destination-array-is-a-copy-of-the-source-array
                             no-error-during-program-execution
                             after-the-copy-conditions
                             preconditions
                             clk post-clk pre-clk
                             (clk) (post-clk) (pre-clk)
                             force (force))))))

;; ======================================================================
