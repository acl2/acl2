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

(set-irrelevant-formals-ok t)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

;; (0) Factorial program:

(defconst *factorial_recursive*
  '(#x85 #xff                             ;;  test %edi,%edi
    #xb8 #x01 #x00 #x00 #x00              ;;  mov $0x1,%eax
    #x74 #x0f                             ;;  je <factorial_recursive+0x18>
    #x0f #x1f #x80 #x00 #x00 #x00 #x00    ;;  nopl 0x0(%rax)
    #x0f #xaf #xc7                        ;;  imul %edi,%eax
    #x83 #xef #x01                        ;;  sub $0x1,%edi
    #x75 #xf8))                           ;;  jne <factorial_recursive+0x10>

;; ======================================================================

;; (0.1) But first, some misc. arithmetic/bitops-like lemmas --- maybe
;; should generalize enough so that I can move them to
;; proofs/utilities/basics.lisp?

(local
 (defthm logcons-and-+-bit-1
   (implies (or (and (equal b1 -1)
                     (equal b2 1))
                (and (equal b1 1)
                     (equal b2 0)))
            (equal (+ b1 (logcons b2 x))
                   (logcons (+ b1 b2) x)))
   :hints (("Goal" :in-theory (e/d* (logcons) ())))))

(local
 (defthm logext-n-x-1-<-x-helper-1
   (implies (and (integerp x)
                 (<= (logext (+ -1 n) (logcdr x))
                     (logcdr x)))
            (< (+ -1 (logcons 0 (logext (+ -1 n) (logcdr x))))
               x))
   :hints (("Goal" :in-theory (e/d* (logcons) ())))))


(local
 (defthm logext-n-x-1-<-x-helper-2
   (implies (and (integerp x)
                 (< (+ -1 (logext (+ -1 n) (logcdr x)))
                    (logcdr x)))
            (< (+ -1
                  (logcons (logcar x)
                           (logext (+ -1 n) (logcdr x))))
               x))
   :hints (("Goal"
            :cases ((equal (logcar x) 0))
            :in-theory (e/d* (bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs)
                             ())))))

(defthm logext-n-x-1-<-x
  (implies (natp x)
           (< (+ -1 (logext n x)) x))
  :hints (("Goal"
           :in-theory (e/d* (bitops::ihsext-inductions
                             bitops::ihsext-recursive-redefs)
                            ())))
  :rule-classes :linear)

(local
 (defthm pull-out-logcons-from-loghead
   (implies (posp n)
            (equal (loghead n (logcons 0 x))
                   (logcons 0 (loghead (1- n) x))))
   :hints (("Goal"
            :in-theory (e/d* (bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs)
                             ())))))

(defthm loghead-n-x-<-x
  (implies (natp x)
           (<= (loghead n x) x))
  :hints (("Goal"
           :in-theory (e/d* (bitops::ihsext-inductions
                             bitops::ihsext-recursive-redefs)
                            ())))
  :rule-classes :linear)

(defthm loghead-n-1-logext-n-x-<-x
  (implies (and (posp x)
                (posp n))
           (< (loghead n (+ -1 (logext n x))) x))
  :hints (("Goal"
           :cases ((equal (logcar x) 0))
           :in-theory (e/d* (bitops::ihsext-inductions
                             bitops::ihsext-recursive-redefs)
                            ())))
  :rule-classes :linear)

(defthm bool->bit-logbitp-m-x-where-m->=integer-length-x
  (implies (and (natp x)
                (equal n (integer-length x))
                (natp m)
                (<= n m))
           (equal (bool->bit (logbitp m x)) 0))
  :hints (("Goal" :in-theory
           (e/d* (acl2::logbitp**
                  acl2::integer-length**
                  acl2::ihsext-inductions)
                 ()))))

(defthm loghead-<=0-of-x
  (implies (and (< i 0)
                (integerp i))
           (equal (loghead i x) 0))
  :hints (("Goal" :in-theory (e/d () ()))))

(defthm logand-n-n-equal-n
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logand n n) n)))

;; ======================================================================

;; (1) Specification: defining the expected inputs and the desired
;; output, f:

(defun ok-inputs (n x86)
  (declare (xargs :stobjs (x86)))
  (and (x86p x86)
       (natp n)
       (< n 13)))

(defun f (n)
  (if (zp n)
      1
    (* n (f (- n 1)))))

(defun fact-init-x86-state (n addr x86)
  (declare (xargs :stobjs (x86)
                  :guard (and (natp n)
                              (canonical-address-p addr))
                  :guard-hints (("Goal" :in-theory
                                 (e/d (canonical-address-p) ())))))
  (and (x86p x86)
       (n32p n)
       (equal (ms x86) nil)
       (equal (fault x86) nil)
       (equal n (rgfi *rdi* x86))
       (64-bit-modep x86)
       (app-view x86)
       (canonical-address-p addr)
       (canonical-address-p (+ addr (len *factorial_recursive*)))
       (program-at addr *factorial_recursive* x86)))

(defthm fact-init-x86-state-forward-chaining
  (implies (fact-init-x86-state n addr x86)
           (and (x86p x86)
                (natp n)
                (n32p n)
                (equal (ms x86) nil)
                (equal (fault x86) nil)
                (equal n (rgfi *rdi* x86))
                (64-bit-modep x86)
                (app-view x86)
                (canonical-address-p addr)
                (canonical-address-p (+ addr (len *factorial_recursive*)))
                (program-at addr *factorial_recursive* x86)))
  :rule-classes :forward-chaining)

(in-theory (e/d () (fact-init-x86-state)))

;; ======================================================================

;; (2) Algorithm:

(defun fact-algorithm-simple (n a)
  (if (posp n)
      (let* ((a (* a n))
             (n (- n 1)))
        (if (not (equal n 0))
            (fact-algorithm-simple n a)
          a))
    1))

(defun fact-algorithm (n a)
  (if (posp n)
      (let* ((a (n32 (* (n32-to-i32 a) (n32-to-i32 n))))
             (n (n32 (- (n32-to-i32 n) 1))))
        (if (not (equal n 0))
            (fact-algorithm n a)
          a))
    1))

(defthm-unsigned-byte-p n32p-fact-algorithm
  :hyp (and (n32p n)
            (n32p a))
  :bound 32
  :concl (fact-algorithm n a)
  :gen-linear t
  :gen-type t)

(defthmd fact-algorithm-and-fact-algorithm-simple
  (implies (and (natp n)
                (< n 13))
           (equal (fact-algorithm n 1)
                  (fact-algorithm-simple n 1)))
  :hints (("Goal" :cases ((equal n 0)
                          (equal n 1)
                          (equal n 2)
                          (equal n 3)
                          (equal n 4)
                          (equal n 5)
                          (equal n 6)
                          (equal n 7)
                          (equal n 8)
                          (equal n 9)
                          (equal n 10)
                          (equal n 11)
                          (equal n 12)))))

(defun-nx whatever-it-is (x86)
  (let* ((x86-3 (x86-run 3 x86))
         (x86 (unsafe-!undef (undef x86-3) x86))
         (x86 (!rflags (rflags x86-3) x86)))
    x86))

(defun loop-all-induction (n a loop-addr x86)
  (declare (xargs :stobjs (x86)
                  :verify-guards nil))
  (if (posp n)
      (let* ((x86 (whatever-it-is x86))
             (x86 (!rgfi *rax* (n32 (* (n32-to-i32 a) (n32-to-i32 n))) x86))
             (x86 (!rgfi *rdi* (n32 (- (n32-to-i32 n) 1)) x86)))
        (if (equal n 1)
            (let ((x86 (!rip (+ loop-addr 8) x86)))
              x86)
          (let ((x86 (!rip loop-addr x86)))
            (loop-all-induction (n32 (- (n32-to-i32 n) 1))
                                (n32 (* (n32-to-i32 a) (n32-to-i32 n)))
                                loop-addr
                                x86))))
    x86))

(defthm x86p-loop-all-induction
  (implies (and (natp n)
                (n32p a)
                (canonical-address-p addr)
                (canonical-address-p (+ addr (len *factorial_recursive*)))
                (x86p x86))
           (x86p (loop-all-induction n a addr x86)))
  :hints (("Goal" :in-theory (e/d (signed-byte-p) ()))))

(defthm rgfi-rax-loop-all-induction
  (implies (and (posp n)
                (n32p a)
                (canonical-address-p addr)
                (canonical-address-p (+ addr (len *factorial_recursive*)))
                (x86p x86))
           (equal (xr :rgf *rax* (loop-all-induction n a addr x86))
                  (fact-algorithm n a)))
  :hints (("Goal" :in-theory (e/d (signed-byte-p) ()))))

(in-theory (e/d () (rgfi-rax-loop-all-induction)))

;; ======================================================================

;; (3) Prove that the algorithm satisfies the specification: first
;; prove that helper is appropriately related to f and then that
;; fn is f on ok-inputs.

(defthm fact-algorithm-simple-and-f-1
  (implies (and (natp n)
                (posp n)
                (natp a))
           (equal (fact-algorithm-simple n a)
                  (* a (f n)))))

(defthm fact-algorithm-simple-and-f
  (implies (natp n)
           (equal (fact-algorithm-simple n 1)
                  (f n))))

(defthm fact-algorithm-and-f
  (implies (and (natp n)
                (< n 13))
           (equal (fact-algorithm n 1)
                  (f n)))
  :hints (("Goal" :use ((:instance fact-algorithm-and-fact-algorithm-simple)))))

(in-theory (disable fact-algorithm-simple-and-f-1
                    fact-algorithm-simple-and-f
                    fact-algorithm-and-f))

;; ======================================================================

;; (4) Define the ACL2 function that clocks this program.

(defun fact-preamble-n=0   () 3)
(defun fact-preamble-n!=0  () 4)

(defun loop-clk (n a)
  (if (zp n) ;; We are never going to be in the loop if n = 0.
      0
    (if (eql n 1)
        3
      (clk+ 3
            (loop-clk (n32 (- (n32-to-i32 n) 1))
                      (n32 (* (n32-to-i32 a) (n32-to-i32 n))))))))

(defun clk (n a)
  (if (zp n)
      (fact-preamble-n=0)
    (clk+ (fact-preamble-n!=0)
          (loop-clk n a))))

;; ======================================================================

;; (5) Prove that the code (*factorial_recursive*) implements the
;; algorithm:

(encapsulate

  ()

  (local (include-book "centaur/gl/gl" :dir :system))

  (local
   (def-gl-thm loop-effects-helper-1
     :hyp (and (not (equal rdi 1))
               (unsigned-byte-p 32 rdi))
     :concl (equal (equal (loghead 32 (+ -1 (logext 32 rdi))) 0)
                   nil)
     :g-bindings
     `((rdi   (:g-number ,(increasing-list 0 2 33))))))

  (defthm loop-effects-helper
    (implies (and (not (equal rdi 1))
                  (unsigned-byte-p 32 rdi))
             (equal (equal (loghead 32 (+ -1 (logext 32 rdi))) 0)
                    nil))))

(local
 (defthm xw-of-xr-alt
   ;; Contrast with xw-of-xr.
   (implies (equal old-val (xr fld idx x86))
            (equal (xw fld idx old-val x86) x86))))

(defthm loop-effects
  ;; imul %edi,%eax
  ;; sub $0x1,%edi
  ;; jne 400600
  (implies (and
            (equal addr (- (rip x86) #x10))
            (fact-init-x86-state n addr x86)
            (equal loop-addr (+ #x10 addr))
            (n32p a)
            (posp n)
            (equal a (rgfi *rax* x86)))
           (equal (x86-run (loop-clk n a) x86)
                  (let* ((x86 (loop-all-induction n a loop-addr x86))
                         (x86 (xw :rip nil (+ #x18 addr) x86)))
                    x86)))
  :hints (("Goal"
           :induct (loop-all-induction n a loop-addr x86)
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             x86-operation-mode
                             imul-spec             ;; IMUL
                             imul-spec-32          ;; IMUL
                             gpr-sub-spec-4        ;; SUB
                             jcc/cmovcc/setcc-spec ;; JNE
                             one-byte-opcode-execute
                             two-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             check-instruction-length
                             write-user-rflags
                             riml-size
                             riml08
                             rml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Registers:
                             rr32
                             wr32
                             signed-byte-p
                             fact-init-x86-state)
                            (bitops::logior-equal-0
                             negative-logand-to-positive-logand-with-integerp-x
                             not
                             (:linear loghead-n-x-<-x)
                             (:linear logext-n-x-1-<-x)
                             (:rewrite acl2::natp-rw)
                             (:rewrite acl2::<-*-0)
                             (:rewrite acl2::natp-posp--1)
                             (:rewrite acl2::natp-when-integerp)
                             (:rewrite acl2::natp-when-gte-0)
                             (:rewrite acl2::natp-*)
                             (:rewrite get-prefixes-opener-lemma-group-4-prefix)
                             (:rewrite get-prefixes-opener-lemma-group-3-prefix)
                             (:rewrite get-prefixes-opener-lemma-group-2-prefix)
                             (:rewrite get-prefixes-opener-lemma-group-1-prefix))))))

(in-theory (e/d (subset-p) (loop-clk)))

(defthm factorial-preamble-n=0-post-cond
  (implies (fact-init-x86-state 0 (rip x86) x86)

           (and (fact-init-x86-state 0 (xr :rip nil x86) (x86-run (fact-preamble-n=0) x86))

                (equal (xr :rgf *rax* (x86-run (fact-preamble-n=0) x86)) 1)
                (equal (xr :rip      nil  (x86-run (fact-preamble-n=0) x86)) (+ #x18 (xr :rip nil x86)))
                (equal (xr :ms       nil  (x86-run (fact-preamble-n=0) x86)) nil)
                (equal (xr :fault    nil  (x86-run (fact-preamble-n=0) x86)) nil)
                (equal (xr :app-view nil (x86-run (fact-preamble-n=0) x86))
                       (xr :app-view nil x86))))

  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             x86-operation-mode
                             one-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             check-instruction-length
                             write-user-rflags
                             riml-size
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Spec functions:
                             gpr-and-spec-4
                             jcc/cmovcc/setcc-spec
                             rme-size
                             rime-size
                             rml08
                             rml32
                             riml32
                             rr32
                             wr32
                             signed-byte-p
                             fact-init-x86-state)
                            (bitops::logior-equal-0
                             not
                             loop-effects)))))

(defthm factorial-preamble-n=0-rip-fluff
  (implies (fact-init-x86-state 0 (rip x86) x86)
           (equal (xw :rip nil (+ 24 (xr :rip nil x86))
                      (x86-run (fact-preamble-n=0) x86))
                  (x86-run (fact-preamble-n=0) x86)))

  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             x86-operation-mode
                             one-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             check-instruction-length
                             write-user-rflags
                             riml-size
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Spec functions:
                             gpr-and-spec-4
                             jcc/cmovcc/setcc-spec
                             rme-size
                             rime-size
                             rml08
                             rml32
                             riml32
                             rr32
                             wr32
                             signed-byte-p
                             fact-init-x86-state)
                            (bitops::logior-equal-0
                             not
                             loop-effects)))))

(defthm factorial-preamble-n!=0-post-cond
  (implies (and (fact-init-x86-state n (xr :rip nil x86) x86)
                (not (equal (rgfi *rdi* x86) 0)))

           (and (fact-init-x86-state n (xr :rip nil x86) (x86-run (fact-preamble-n!=0) x86))

                (equal (xr :rgf *rax* (x86-run (fact-preamble-n!=0) x86)) 1)
                (equal (xr :rip    nil  (x86-run (fact-preamble-n!=0) x86)) (+ #x10 (xr :rip nil x86)))
                (equal (xr :ms     nil  (x86-run (fact-preamble-n!=0) x86)) nil)
                (equal (xr :fault  nil  (x86-run (fact-preamble-n!=0) x86)) nil)
                (equal (xr :app-view nil (x86-run (fact-preamble-n!=0) x86))
                       (xr :app-view nil x86))))

  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             x86-operation-mode
                             one-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             check-instruction-length
                             write-user-rflags
                             riml-size
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Spec functions:
                             gpr-and-spec-4
                             jcc/cmovcc/setcc-spec
                             rme-size
                             rime-size
                             rml08
                             rml32
                             riml32
                             rr32
                             wr32
                             signed-byte-p
                             fact-init-x86-state)
                            (bitops::logior-equal-0
                             not
                             loop-effects)))))

(defthm factorial-preamble-n!=0-rip-fluff
  (implies (and (<= n 0)
                (fact-init-x86-state n (rip x86) x86)
                (not (equal n 0)))
           (equal (xw :rip nil (+ 24 (xr :rip nil x86))
                      (x86-run (fact-preamble-n!=0) x86))
                  (x86-run (fact-preamble-n=0) x86)))

  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             x86-operation-mode
                             one-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             write-user-rflags
                             rme-size
                             rime-size
                             riml-size
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Spec functions:
                             gpr-and-spec-4
                             jcc/cmovcc/setcc-spec
                             rml08
                             rml32
                             riml32
                             rr32
                             wr32
                             signed-byte-p
                             fact-init-x86-state)
                            (bitops::logior-equal-0
                             not
                             loop-effects)))))
(in-theory (e/d ()
                (fact-preamble-n=0
                 fact-preamble-n!=0
                 (fact-preamble-n=0)
                 (fact-preamble-n!=0))))

(defthm factorial-effects
  (implies (and (fact-init-x86-state n addr x86)
                (equal addr (rip x86)))
           (equal (x86-run (clk n 1) x86)
                  (let* ((x86 (if (equal n 0)
                                  (x86-run (fact-preamble-n=0) x86)
                                (x86-run (fact-preamble-n!=0) x86)))
                         (x86 (loop-all-induction n 1 (+ #x10 addr) x86))
                         (x86 (!rip (+ #x18 addr) x86)))
                    x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             x86-operation-mode
                             one-byte-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             x86-operand-from-modr/m-and-sib-bytes
                             write-user-rflags
                             riml-size
                             riml08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             n32-to-i32
                             ;; Flags:
                             zf-spec
                             ;; Spec functions:
                             gpr-and-spec-4
                             jcc/cmovcc/setcc-spec
                             rml32
                             riml32
                             rr32
                             wr32
                             signed-byte-p)
                            (bitops::logior-equal-0
                             not)))
          ("Subgoal 1"
           :in-theory (e/d ()
                           (loop-effects
                            x86-run-plus))
           :use ((:instance loop-effects
                            (x86 (x86-run (fact-preamble-n!=0) x86))
                            (a 1)
                            (addr (rip x86))
                            (loop-addr (+ #x10 (rip x86))))
                 (:instance x86-run-plus
                            (n1 (fact-preamble-n!=0))
                            (n2 (loop-clk n 1))
                            (x86 x86))))))

(in-theory (e/d () (clk)))

;; ======================================================================

;; (6) Put the two steps together to get correctness, i.e., program
;; satisfies its specification f.

(defthmd factorial-halted
  (implies (and (ok-inputs n x86)
                (fact-init-x86-state n addr x86)
                (equal (rip x86) addr)
                (equal x86-fact (x86-run (clk n 1) x86)))
           (equal (rip x86-fact)
                  (+ 24 (rip x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance factorial-effects))
           :in-theory (e/d (fact-init-x86-state)
                           (f
                            factorial-effects
                            x86-run-opener-not-ms-not-zp-n
                            x86-run-plus-1
                            x86-run-plus
                            clk (clk)
                            loop-all-induction)))))

(defthmd rgfi-rax-loop-all-induction-fluff
  (implies
   (and (posp n)
        (n32p a)
        (canonical-address-p addr)
        (x86p x86))
   (equal (rgfi *rax*
                (!rip (+ 24 (rip x86))
                      (loop-all-induction n a addr x86)))
          (fact-algorithm n a)))
  :hints (("Goal" :in-theory (e/d (signed-byte-p) ()))))

(defthm factorial-correct-helper
  (implies (and (ok-inputs n x86)
                (fact-init-x86-state n addr x86)
                (equal (rip x86) addr)
                (equal x86-fact (x86-run (clk n 1) x86)))
           (and (equal (rgfi *rax* x86-fact)
                       (fact-algorithm n 1))
                (equal (rip x86-fact)
                       (+ #x18 addr))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance factorial-effects)
                 (:instance factorial-halted)
                 (:instance rgfi-rax-loop-all-induction-fluff
                            (addr (+ #x10 (rip x86)))
                            (a 1)
                            (n n)
                            (x86 (x86-run (fact-preamble-n!=0) x86))))
           :in-theory (e/d
                       (rml08
                        fact-init-x86-state)
                       (f
                        program-at
                        factorial-effects
                        x86-run-opener-not-ms-not-zp-n
                        x86-run-plus-1
                        x86-run-plus
                        canonical-address-p
                        factorial-preamble-n=0-rip-fluff
                        (clk) clk)))))

(defthm factorial-correct
  (implies (and (ok-inputs n x86)
                (fact-init-x86-state n addr x86)
                (equal (rip x86) addr)
                (equal x86-fact (x86-run (clk n 1) x86)))
           (and (equal (rgfi *rax* x86-fact)
                       (f n))
                (equal (rip x86-fact)
                       (+ #x18 addr))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d
                       ()
                       (f
                        factorial-effects
                        x86-run-opener-not-ms-not-zp-n
                        x86-run-plus-1
                        x86-run-plus))
           :use ((:instance factorial-correct-helper)
                 (:instance fact-algorithm-and-f)))))

;; ======================================================================
