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

(local (include-book "centaur/gl/gl" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; bool isPowerOfTwo? (long int v) {
;;   bool f;
;;   f = v && !(v & (v - 1));
;;   return f;
;; }


;; GCC O2 Optimization
;; 0000000100000ec0 <_powerOfTwo>:
;;    100000ec0:	55                      push   %rbp
;;    100000ec1:	48 89 e5                mov    %rsp,%rbp
;;    100000ec4:	48 85 ff                test   %rdi,%rdi
;;    100000ec7:	74 0c                   je     100000ed5 <_powerOfTwo+0x15>
;;    100000ec9:	48 8d 47 ff             lea    -0x1(%rdi),%rax
;;    100000ecd:	48 85 c7                test   %rax,%rdi
;;    100000ed0:	0f 94 c0                sete   %al
;;    100000ed3:	eb 02                   jmp    100000ed7 <_powerOfTwo+0x17>
;;    100000ed5:	31 c0                   xor    %eax,%eax
;;    100000ed7:	5d                      pop    %rbp
;;    100000ed8:	c3                      retq
;;    100000ed9:	0f 1f 80 00 00 00 00    nopl   0x0(%rax)

(defconst *program*
  '(
    #x55                               ;; push   %rbp
    #x48 #x89 #xe5                     ;; mov    %rsp,%rbp
    #x48 #x85 #xff                     ;; test   %rdi,%rdi
    #x74 #x0c                          ;; je     100000ed5 <_powerOfTwo+0x15>
    #x48 #x8d #x47 #xff                ;; lea    -0x1(%rdi),%rax
    #x48 #x85 #xc7                     ;; test   %rax,%rdi
    #x0f #x94 #xc0                     ;; sete   %al
    #xeb #x02                          ;; jmp    100000ed7 <_powerOfTwo+0x17>
    #x31 #xc0                          ;; xor    %eax,%eax
    #x5d                               ;; pop    %rbp
    #xc3                               ;; retq
    ))

(defconst *l* (len *program*))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defun power-of-2-p (x)
    (if (zp x)
        nil
      (if (equal x 1)
          t
        (if (zp (mod x 2))
            (power-of-2-p (floor x 2))
          nil))))

  (defun compute-power-of-2 (x count)
    (declare (xargs :measure (power-of-2-measure x)
                    :guard (natp count)))
    ;; Find the number n such that x approx.== 2^n.
    (if (natp x)
        (if (<= x 1)
            count
          (compute-power-of-2 (* 1/2 x) (1+ count)))
      count))

  (defthm integerp-compute-power-of-2
    (implies (integerp count)
             (integerp (compute-power-of-2 x count)))
    :rule-classes :type-prescription)

  (defthm natp-compute-power-of-2
    (implies (natp count)
             (natp (compute-power-of-2 x count)))
    :rule-classes :type-prescription)

  (local
   (defthm compute-power-of-2-and-expt
     (implies
      ;; natp would lead to a stronger rule, but I want a weak one here.
      (posp count)
      (equal (expt 2 (compute-power-of-2 x count))
             (expt 2 (+ 1 (compute-power-of-2 x (1- count))))))))

  (defthm if-power-of-2-p-returns-t-then-x-is-indeed-a-power-of-2
    ;; If (power-of-2-p x) is t, then there exists a natural number n
    ;; such that x is equal to (expt 2 n).
    (implies (and (power-of-2-p x)
                  (natp x))
             (equal (expt 2 (compute-power-of-2 x 0)) x)))

  (defthm power-of-2-p-returns-t-for-x=2^n
    ;; Every number x == 2^n, where n is a natural number,
    ;; satisfies power-of-2-p.
    (implies (and (natp n)
                  (equal x (expt 2 n)))
             (power-of-2-p x))
    :hints (("Goal" :in-theory (e/d* (expt) ())))))

(local
 (def-gl-thm program-effects-helper-1
   :hyp (and (unsigned-byte-p 64 x)
             (power-of-2-p x))
   :concl (equal (logand x (+ -1 x)) 0)
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm program-effects-helper-2
   :hyp (and (unsigned-byte-p 64 x)
             (not (equal x 0))
             (not (power-of-2-p x)))
   :concl (equal (equal (logand x (+ -1 x)) 0) nil)
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm program-effects-helper-3
   :hyp (and (signed-byte-p 64 x)
             (power-of-2-p (loghead 64 x)))
   :concl (equal (logand (loghead 64 x)
                         (loghead 64 (+ -1 x)))
                 0)
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm program-effects-helper-4
   :hyp (and (signed-byte-p 64 x)
             (< 0 (loghead 64 x))
             (not (power-of-2-p (loghead 64 x))))
   :concl (not (equal (logand (loghead 64 x)
                              (loghead 64 (+ -1 x)))
                      0))
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm power-of-2-p-result-helper-1
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (loghead 8 (logior 1 (logext 64 (bitops::logsquash 8 (+ -1 x)))))
                 1)
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm power-of-2-p-result-helper-2
   :hyp (signed-byte-p 64 x)
   :concl (signed-byte-p 64 (logior 1 (bitops::logsquash 8 (logext 64 (+ -1 x)))))
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

(local
 (def-gl-thm power-of-2-p-result-helper-3
   :hyp (signed-byte-p 64 x)
   :concl (signed-byte-p 64 (bitops::logsquash 8 (logext 64 (+ -1 x))))
   :g-bindings
   `((x    (:g-number ,(gl-int 0 1 65))))))

;; ======================================================================

(defun-nx preconditions (x86)
  (and
   ;; The x86 state is well-formed.
   (x86p x86)
   ;; Alignment checking is turned off.
   (not (alignment-checking-enabled-p x86))
   ;; The model is operating in 64-bit mode.
   (64-bit-modep x86)
   ;; The model is operating in the application-level view.
   (app-view x86)
   ;; The program is located at linear addresses ranging from (rip
   ;; x86) to (+ -1 (len *program*) (rip x86)).
   (program-at (rip x86) *program* x86)
   ;; The addresses where the program is located are canonical.
   (canonical-address-p (rip x86))
   (canonical-address-p (+ (len *program*) (rip x86)))
   ;; The initial state is error-free.
   (equal (ms x86) nil)
   (equal (fault x86) nil)
   ;; Stack addresses are canonical.
   (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
   (canonical-address-p (xr :rgf *rsp* x86))
   (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
   ;; Return address is canonical.
   (canonical-address-p
    (logext 64 (mv-nth 1 (rb 8 (xr :rgf *rsp* x86) :r x86))))
   ;; Program and stack are disjoint.
   (separate
    :x *l* (xr :rip 0 x86)
    :w  8  (+ -8 (xr :rgf *rsp* x86)))
   (unsigned-byte-p 64 (rr64 *rdi* x86))))

(defun is-power-of-2-clock () 10)

(defun is-not-power-of-2-clock (x)
  (if (zp x) 7 10))

(defthm power-of-2-p-result
  (implies (and (preconditions x86)
                (power-of-2-p (rr64 *rdi* x86)))
           (equal (loghead 8 (xr :rgf *rax* (x86-run (is-power-of-2-clock) x86)))
                  1))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             jcc/cmovcc/setcc-spec
                             gpr-and-spec-8
                             gpr-xor-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-to-reg/mem$
                             wr08
                             wr32
                             wr64
                             rr32
                             rr64
                             rime-size
                             rme-size
                             wime-size
                             wme-size
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
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             ;; Flags
                             write-user-rflags
                             zf-spec)
                            (canonical-address-p
                             signed-byte-p)))))

(defthm not-power-of-2-p-result
  (implies (and (preconditions x86)
                (not (power-of-2-p (rr64 *rdi* x86))))
           (equal (loghead
                   8
                   (xr :rgf *rax*
                       (x86-run (is-not-power-of-2-clock (rr64 *rdi* x86)) x86)))
                  0))
  :hints (("Goal"
           :do-not-induct t
           :cases (equal (rgfi *rdi* x86) 0)
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             jcc/cmovcc/setcc-spec
                             gpr-and-spec-8
                             gpr-xor-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-to-reg/mem$
                             wr08
                             wr32
                             wr64
                             rr32
                             rr64
                             rime-size
                             rme-size
                             wime-size
                             wme-size
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
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             ;; Flags
                             write-user-rflags
                             zf-spec)
                            (canonical-address-p
                             not
                             signed-byte-p)))))

;; ======================================================================
