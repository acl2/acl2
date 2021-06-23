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
(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* (x86-operation-mode
                         rime-size
                         rme-size
                         wime-size
                         wme-size)
                        (las-to-pas
                         xr-fault-wb-in-system-level-marking-view
                         xr-fault-wb-in-sys-view))))

;; ======================================================================

;; Here is the sub-routine:
;; void copyData (int* src, int* dst, unsigned int n) {

;;   int* dstEnd = dst + n;

;;   while (dst != dstEnd)
;;     *dst++ = *src++;

;; }

;; O1 optimization:
;; 0000000000000000 <_copyData>:
;;    0:	55                      push   %rbp
;;    1:	48 89 e5                mov    %rsp,%rbp
;;    4:	85 d2                   test   %edx,%edx
;;    6:	74 1a                   je     22 <_copyData+0x22>
;;    8:	89 d0                   mov    %edx,%eax
;;    a:	48 c1 e0 02             shl    $0x2,%rax
;;    e:	66 90                   xchg   %ax,%ax
;;   10:	8b 0f                   mov    (%rdi),%ecx
;;   12:	48 83 c7 04             add    $0x4,%rdi
;;   16:	89 0e                   mov    %ecx,(%rsi)
;;   18:	48 83 c6 04             add    $0x4,%rsi
;;   1c:	48 83 c0 fc             add    $0xfffffffffffffffc,%rax
;;   20:	75 ee                   jne    10 <_copyData+0x10>
;;   22:	5d                      pop    %rbp
;;   23:	c3                      retq

(defconst *copyData* ;; 15 instructions
  '(
    #x55                ;; push   %rbp                        1
    #x48 #x89 #xe5      ;; mov    %rsp,%rbp                   2
    #x85 #xd2           ;; test   %edx,%edx                   3
    #x74 #x1a           ;; je     22 <_copyData+0x22>         4 (jump if ZF = 1)
    #x89 #xd0           ;; mov    %edx,%eax                   5
    #x48 #xc1 #xe0 #x02 ;; shl    $0x2,%rax                   6
    #x66 #x90           ;; xchg   %ax,%ax                     7
    #x8b #x0f           ;; mov    (%rdi),%ecx                 8
    #x48 #x83 #xc7 #x04 ;; add    $0x4,%rdi                   9
    #x89 #x0e           ;; mov    %ecx,(%rsi)                10
    #x48 #x83 #xc6 #x04 ;; add    $0x4,%rsi                  11
    #x48 #x83 #xc0 #xfc ;; add    $0xfffffffffffffffc,%rax   12
    #x75 #xee           ;; jne    10 <_copyData+0x10>        13 (jump if ZF = 0)
    #x5d                ;; pop    %rbp                       14
    #xc3                ;; retq                              15
    ))

(defconst *prog-len* (len *copyData*))

;; Some important registers:

;; EDX: n
;; RSI: Destination address
;; RDI: Source address

;; ======================================================================

;; Some GL Theorems:

(encapsulate
  ()
  (local (include-book "centaur/gl/gl" :dir :system))

  (defthm-using-gl loop-clk-measure-helper
    :hyp (and (signed-byte-p 64 m)
              (<= 4 m))
    :concl (< (loghead 64 (+ #xfffffffffffffffc m)) m)
    :g-bindings (gl::auto-bindings (:int m 64))
    :rule-classes :linear)

  (defthm-using-gl effects-copyData-loop-helper-1
    :hyp (and (<= 4 m)
              (unsigned-byte-p 34 m))
    :concl (equal (logext 64 (+ #xfffffffffffffffc m))
                  (loghead 64 (+ #xfffffffffffffffc m)))
    :g-bindings (gl::auto-bindings (:nat m 34)))

  (defthm-using-gl effects-copyData-loop-helper-6
    :hyp (canonical-address-p src/dst)
    :concl (equal (logext 64 (+ 4 (loghead 64 src/dst)))
                  (+ 4 src/dst))
    :g-bindings (gl::auto-bindings (:int src/dst 64)))

  (defthm-using-gl effects-copyData-loop-helper-7
    :hyp (and (canonical-address-p src/dst)
              (canonical-address-p (+ m src/dst))
              (< 4 m)
              (equal (mod m 4) 0)
              (unsigned-byte-p 34 m))
    :concl (canonical-address-p (+ 4 src/dst (loghead 64 (+ #xfffffffffffffffc m))))
    :g-bindings (gl::auto-bindings (:mix (:int m 64)
                                         (:int src/dst 64))))

  (defthm-using-gl effects-copyData-loop-helper-9
    :hyp (and (< 4 m)
              (unsigned-byte-p 34 m))
    :concl (not (equal (loghead 64 (+ #xfffffffffffffffc m)) 0))
    :g-bindings (gl::auto-bindings (:nat m 34))
    :rule-classes (:forward-chaining :rewrite))

  (defthm-using-gl effects-copyData-loop-helper-11
    :hyp (and (< 4 m)
              (equal (mod m 4) 0)
              (unsigned-byte-p 34 m))
    :concl (equal (loghead 64 (+ #xfffffffffffffffc m))
                  (+ -4 m))
    :g-bindings (gl::auto-bindings (:nat m 34)))

  (defthm-using-gl effects-copyData-loop-helper-13
    :hyp (and (equal (mod k 4) 0)
              (unsigned-byte-p 34 k))
    :concl (equal (mod (+ 4 k) 4) 0)
    :g-bindings (gl::auto-bindings (:nat k 34)))

  (defthm-using-gl effects-copyData-loop-helper-14
    :hyp (and (< 4 m)
              (equal (mod m 4) 0)
              (unsigned-byte-p 34 m))
    :concl (equal (mod (+ -4 m) 4) 0)
    :g-bindings (gl::auto-bindings (:nat m 34)))

  (defthm-using-gl effects-copyData-loop-helper-15
    :hyp (and (equal (loghead 2 m) 0)
              (canonical-address-p m))
    :concl (equal (loghead 2 (+ 4 m)) 0)
    :g-bindings (gl::auto-bindings (:int m 48)))

  (defthm-using-gl effects-copyData-loop-helper-16
    :hyp (and (equal (loghead 3 m) 0)
              (canonical-address-p m))
    :concl (equal (loghead 3 (+ 8 m)) 0)
    :g-bindings (gl::auto-bindings (:int m 48)))

  (in-theory (e/d ()
                  (effects-copyData-loop-helper-11
                   effects-copyData-loop-helper-14))))

;; ======================================================================

(defun-nx source-bytes (k src-addr x86)
  (mv-nth 1 (rb k (+ (- k) src-addr) :r x86)))

(defun-nx destination-bytes (k dst-addr x86)
  (mv-nth 1 (rb k (+ (- k) dst-addr) :r x86)))

(defun-nx loop-invariant (k m addr x86)
  ;; The initial value of m is (ash n 2), where n is the same n as defined in
  ;; preconditions later in this book.

  ;; k: number of bytes already copied (in previous loop iterations)
  ;;    this will increase by 4 in every iteration
  ;; m: number of bytes to be copied
  ;;    this will decrease by 4 in every iteration

  (and (x86p x86)
       (64-bit-modep x86)
       (xr :app-view nil x86)
       (equal (xr :ms nil x86) nil)
       (equal (xr :fault nil x86) nil)
       (unsigned-byte-p 34 m)
       (equal (mod m 4) 0)
       (unsigned-byte-p 34 k)
       (equal (mod k 4) 0)
       (unsigned-byte-p 34 (+ m k))
       (equal (xr :rgf *rax* x86) m)
       ;; Stack addresses are canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       ;; Return address of the copyData sub-routine is canonical.
       (canonical-address-p
        (logext 64 (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
       ;; All the destination addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
       (canonical-address-p (+ m (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
       (canonical-address-p (+ m (xr :rgf *rdi* x86)))
       ;; Alignment Checking
       (if (alignment-checking-enabled-p x86)
           ;; rsi and rdi point to doublewords (four bytes), so their
           ;; natural boundary will be addresses divisible by 4.
           (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                (equal (loghead 2 (xr :rgf *rdi* x86)) 0))
         t)
       ;; Memory locations of interest are disjoint.
       (separate
        ;; Program addresses
        :x *prog-len* addr
        ;; Destination addresses
        :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
       (separate
        ;; Return Address
        :r 8 (+ 8 (xr :rgf *rsp* x86))
        ;; Destination Addresses
        :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
       ;; We could modify the following pre-condition to say the following:
       ;; either the source and destination addresses are completely disjoint
       ;; or they are equal. However, the equality of the source and
       ;; destination isn't what we are interested in for this program and so I
       ;; choose to leave that out.
       (separate
        ;; Source Addresses
        :r (+ m k) (+ (- k) (xr :rgf *rdi* x86))
        ;; Destination Addresses
        :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ *prog-len* addr))
       (program-at addr *copyData* x86)
       ;; Values copied in the previous iterations of the loop are unaltered.
       ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
       (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
              (source-bytes      k (xr :rgf *rdi* x86) x86))))

(defun-nx loop-preconditions (k m addr src-addr dst-addr x86)
  (and (loop-invariant k m addr x86)
       ;; At the beginning of every iteration, we have some bytes left to be
       ;; copied.
       (posp m)
       (equal (xr :rgf *rdi* x86) src-addr)
       (equal (xr :rgf *rsi* x86) dst-addr)
       (equal addr (+ -16 (xr :rip nil x86)))))

(defthm loop-preconditions-fwd-chain-to-its-body
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (and (x86p x86)
                (64-bit-modep x86)
                (xr :app-view nil x86)
                (equal (xr :ms nil x86) nil)
                (equal (xr :fault nil x86) nil)
                (unsigned-byte-p 34 m)
                (equal (mod m 4) 0)
                (unsigned-byte-p 34 k)
                (equal (mod k 4) 0)
                (unsigned-byte-p 34 (+ m k))
                (equal (xr :rgf *rax* x86) m)
                ;; Stack addresses are canonical.
                (canonical-address-p (xr :rgf *rsp* x86))
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                ;; Return address of the copyData sub-routine is canonical.
                (canonical-address-p
                 (logext 64 (mv-nth 1 (rb 8 (+ 8 (xr :rgf *rsp* x86)) :r x86))))
                ;; All the destination addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
                (canonical-address-p (+ m (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
                (canonical-address-p (+ m (xr :rgf *rdi* x86)))
                ;; Alignment Checking
                (if (alignment-checking-enabled-p x86)
                    ;; rsi and rdi point to doublewords (four bytes), so their
                    ;; natural boundary will be addresses divisible by 4.
                    (and (equal (loghead 2 (xr :rgf *rsi* x86)) 0)
                         (equal (loghead 2 (xr :rgf *rdi* x86)) 0))
                  t)
                ;; Memory locations of interest are disjoint.
                (separate
                 ;; Program addresses
                 :x *prog-len* addr
                 ;; Destination addresses
                 :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
                (separate
                 ;; Return Address
                 :r 8 (+ 8 (xr :rgf *rsp* x86))
                 ;; Destination Addresses
                 :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
                ;; We could modify the following pre-condition to say the following:
                ;; either the source and destination addresses are completely disjoint
                ;; or they are equal. However, the equality of the source and
                ;; destination isn't what we are interested in for this program and so I
                ;; choose to leave that out.
                (separate
                 ;; Source Addresses
                 :r (+ m k) (+ (- k) (xr :rgf *rdi* x86))
                 ;; Destination Addresses
                 :w (+ m k) (+ (- k) (xr :rgf *rsi* x86)))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ *prog-len* addr))
                (program-at addr *copyData* x86)
                ;; Values copied in the previous iterations of the loop are unaltered.
                ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
                (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
                       (source-bytes      k (xr :rgf *rdi* x86) x86))
                ;; Values copied in the previous iterations of the loop are unaltered.
                ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
                (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
                       (source-bytes      k (xr :rgf *rdi* x86) x86))
                (posp m)
                (equal (xr :rgf *rdi* x86) src-addr)
                (equal (xr :rgf *rsi* x86) dst-addr)
                (equal addr (+ -16 (xr :rip nil x86)))))
  :rule-classes :forward-chaining)

;; ======================================================================

;; Clock functions:

(defun pre-clk (n)
  (if (zp n) 4 7))

(defun loop-clk-base () 6)
(defun loop-clk-recur () 6)

(defun loop-clk (m)
  ;; I use m to refer to (ash n 2).
  (if (signed-byte-p 64 m)
      (let ((new-m (loghead 64 (+ #xfffffffffffffffc m))))
        (if (<= m 4)
            (loop-clk-base)
          (clk+ (loop-clk-recur) (loop-clk new-m))))
    0))

(defun post-clk () 2)

(defun clk (n)
  (if (zp n)
      (pre-clk n)
    (clk+ (pre-clk n)
          (loop-clk (ash n 2)))))

(defun program-clk (n)
  (clk+ (clk n) (post-clk)))

;; ======================================================================

;; Some lemmas for effects theorems:

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm ash-n-2-bound
    (implies (and (< 0 n)
                  (integerp n))
             (<= 4 (ash n 2)))
    :hints (("Goal" :in-theory (e/d* (ash) ())))
    :rule-classes (:rewrite :linear)))

(encapsulate
  ()

  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (defthm mod-thm-1
    (implies (and (equal (mod m 4) 0)
                  (posp m))
             (<= 4 m))
    :rule-classes (:forward-chaining))

  (defthm mod-thm-2
    (implies (natp n)
             (equal (mod (ash n 2) 4) 0))
    :hints (("Goal" :in-theory (e/d* (ash) ())))))

;; ======================================================================
