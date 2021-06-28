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

(include-book "base")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

(defconst *factorial_recursive*
  '(#x85 #xff                             ;;  test %edi,%edi
    #xb8 #x01 #x00 #x00 #x00              ;;  mov $0x1,%eax
    #x74 #x0f                             ;;  je <factorial_recursive+0x18>
    #x0f #x1f #x80 #x00 #x00 #x00 #x00    ;;  nopl 0x0(%rax)
    #x0f #xaf #xc7                        ;;  imul %edi,%eax
    #x83 #xef #x01                        ;;  sub $0x1,%edi
    #x75 #xf8))

(defun-nx factorial-hyps (x86)
  (b* ((program-rip 0)
       (n (rgfi *rdi* x86)))
    (and (x86p x86)
         (64-bit-modep x86)
         (natp n)
         (< n 13)
         (equal (ms x86) nil)
         (equal (fault x86) nil)
         (app-view x86)
         (canonical-address-p program-rip)
         (canonical-address-p (+ program-rip (len *factorial_recursive*)))
         (program-at program-rip *factorial_recursive* x86))))

(acl2::def-model-api
 :run x86-run-ALT               ;; the run function of the model
 :svar x86                      ;; name of state variable
 :stobjp T                      ;;  and whether it's a stobj
 :hyps ((factorial-hyps x86))   ;; invariant to assume about state
 :step x86-fetch-decode-execute ;; name of step function
 :get-pc (lambda (x86) (xr :rip nil x86))     ;; how to fetch the pc
 :put-pc (lambda (v x86) (xw :rip nil v x86)) ;; how to set the pc

 ;; the ``drivers'' below specify how to dive through updaters (and
 ;; constructors) and their accessors
 :updater-drivers (((XW FLD I :VALUE :BASE)
                    (XR FLD I :BASE))
                   ((WB N ADDR R-W-X :VALUE :BASE)
                    (RB N ADDR R-W-X :BASE)))
 :constructor-drivers nil
 :state-comps-and-types
 (((XR :RGF *RDI* X86) (natp (XR :RGF *RDI* X86)))
  ((XR :RGF *RAX* X86) (natp (XR :RGF *RAX* X86)))
  ((XR :RIP  nil  X86) (canonical-address-p (XR :RIP  nil  X86))))
 :callp  nil  ;; recognizer fn for states with pc on call instruction
 :ret-pc nil  ;; how to fetch the return pc after a call
 :returnp nil ;; recognizer for states with pc on return instruction

 :clk+ binary-clk+    ; how to add two clocks
 :name-print-base nil ; base to use for pcs appearing in names
;  (2, 8, 10, or 16)

; how to generate variable names from state comps
 :var-names (((XR :RGF *RDI* X86) "N")
             ((XR :RGF *RAX* X86) "ACC")
             ((XR :RIP nil X86)   "PC")))

(local (in-theory (e/d* (instruction-decoding-and-spec-rules
                         rflag-RoWs-enables
                         x86-operation-mode

                         shr-spec
                         shr-spec-32
                         gpr-and-spec-4
                         gpr-add-spec-1
                         gpr-add-spec-4
                         gpr-add-spec-8
                         gpr-sub-spec-8
                         jcc/cmovcc/setcc-spec
                         imul-spec
                         imul-spec-32
                         gpr-sub-spec-4

                         one-byte-opcode-execute
                         !rgfi-size
                         x86-operand-to-reg/mem
                         wr64
                         wr32
                         rr08
                         rr32
                         rr64
                         rml32
                         rml64
                         wml32
                         wml64
                         rr32
                         x86-operand-from-modr/m-and-sib-bytes
                         rime-size
                         rme-size
                         wime-size
                         wme-size
                         riml-size
                         riml32
                         n32-to-i32
                         n64-to-i64
                         riml08
                         two-byte-opcode-decode-and-execute
                         x86-effective-addr-when-64-bit-modep
                         x86-effective-addr-32/64
                         subset-p
                         ;; Flags
                         write-user-rflags
                         zf-spec)

                        (unsigned-byte-p
                         las-to-pas
                         default-+-2
                         get-prefixes-opener-lemma-group-1-prefix
                         get-prefixes-opener-lemma-group-2-prefix
                         get-prefixes-opener-lemma-group-3-prefix
                         get-prefixes-opener-lemma-group-4-prefix))))

(encapsulate
  ()

  (local (include-book "centaur/gl/gl" :dir :system))

  (defthm-using-gl clk-16-measure-helper
    :hyp (and (natp rdi)
              (< 0 rdi)
              (< rdi 13)
              (not (equal (loghead 32 (+ -1 (logext 32 rdi))) 0)))
    :concl (o< (loghead 32 (+ -1 (logext 32 rdi)))
               (loghead 32 rdi))
    :g-bindings (gl::auto-bindings (:int rdi 64)))

  (defthm-using-gl low-32-bits-of-rdi
    :hyp (and (natp rdi)
              (<= 0 rdi)
              (< rdi 13))
    :concl (equal (equal (loghead 32 rdi) 0)
                  (equal rdi 0))
    :g-bindings (gl::auto-bindings (:int rdi 64)))

  (defthm loghead-<=0-of-x
    (implies (and (< i 0)
                  (integerp i))
             (equal (loghead i x) 0))
    :hints (("Goal" :in-theory (e/d () ())))))

;; The functions clk-16 and sem-16 generated by def-semantics below
;; need to know that the input rdi and rax registers must be greater
;; than 0 in order to terminate.  So, I'm grabbing the output from
;; def-semantics and then hand-editing it.

#||
(acl2::def-semantics
 :init-pc 0
 :focus-regionp (lambda (pc) (and (<= 0 pc) (<= pc 23)))
 :root-name nil ; optional - to change the fn names chosen ;
 ;; :hyps+ ((good-popcount-x86p x86)) ; optional - to strengthen the :hyps of API ;
 :annotations nil ; optional - to modify output generated ;
 )
||#

(PROGN
 (SET-VERIFY-GUARDS-EAGERNESS 0)


 (defun-nx
   CLK-16 (X86)
   (DECLARE (XARGS :STOBJS (X86)
                   :measure (loghead 32 (logext 32 (rgfi *rdi* x86)))))
   (IF
    (and (FACTORIAL-HYPS X86)
         ;; We know the following facts from sem-0.
         (< 0 (xr :rgf *rdi* x86))
         (< 0 (rgfi *rax* x86)))
    (IF
     (EQUAL (LOGHEAD 32
                     (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
            0)
     3
     (BINARY-CLK+
      3
      (CLK-16
       (XW
        :RGF *RAX*
        (LOGHEAD 32
                 (* (LOGEXT 32 (XR :RGF *RAX* X86))
                    (LOGEXT 32 (XR :RGF *RDI* X86))))
        (XW
         :RGF *RDI*
         (LOGHEAD 32
                  (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
         (XW
          :RIP nil 16
          (XW
           :UNDEF nil (+ 4 (NFIX (XR :UNDEF nil X86)))
           (!FLGI
            :CF
            (LOGHEAD 1
                     (BOOL->BIT (< (LOGHEAD 32 (XR :RGF *RDI* X86)) 1)))
            (!FLGI
             :PF
             (PF-SPEC32 (LOGHEAD 32
                                 (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86)))))
             (!FLGI
              :AF
              (SUB-AF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86))
                             1)
              (!FLGI
               :ZF 0
               (!FLGI
                :SF
                (SF-SPEC32 (LOGHEAD 32
                                    (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86)))))
                (!FLGI :OF
                       (OF-SPEC32 (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
                       X86)))))))))))))
    0))

 (defun-nx
   CLK-0 (X86)
   (DECLARE (XARGS :STOBJS (X86)))
   (IF
    (FACTORIAL-HYPS X86)
    (IF
     (EQUAL (LOGHEAD 32 (XR :RGF *RDI* X86)) 0)
     3
     (BINARY-CLK+
      4
      (CLK-16
       (XW
        :RGF *RAX* 1
        (XW
         :RIP nil 16
         (XW
          :UNDEF NIL (+ 1 (NFIX (XR :UNDEF nil X86)))
          (!FLGI
           :CF 0
           (!FLGI
            :PF
            (PF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86)))
            (!FLGI :AF
                   (LOGHEAD 1
                            (CREATE-UNDEF (NFIX (XR :UNDEF nil X86))))
                   (!FLGI :ZF 0
                          (!FLGI :SF
                                 (SF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86)))
                                 (!FLGI :OF 0 X86))))))))))))
    0))

 (defun-nx
   SEM-16 (X86)
   (DECLARE (XARGS :STOBJS (X86)
                   :measure (loghead 32 (logext 32 (rgfi *rdi* x86)))))
   (IF
    (and (FACTORIAL-HYPS X86)
         ;; We know the following facts from sem-0.
         (< 0 (xr :rgf *rdi* x86))
         (< 0 (rgfi *rax* x86)))
    (IF
     (EQUAL (LOGHEAD 32
                     (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
            0)
     (XW
      :RGF *RAX*
      (LOGHEAD 32
               (* (LOGEXT 32 (XR :RGF *RAX* X86))
                  (LOGEXT 32 (XR :RGF *RDI* X86))))
      (XW
       :RGF *RDI* 0
       (XW
        :RIP nil 24
        (XW
         :UNDEF nil (+ 4 (NFIX (XR :UNDEF nil X86)))
         (!FLGI
          :CF
          (LOGHEAD 1
                   (BOOL->BIT (< (LOGHEAD 32 (XR :RGF *RDI* X86)) 1)))
          (!FLGI
           :PF 1
           (!FLGI
            :AF
            (SUB-AF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86))
                           1)
            (!FLGI
             :ZF 1
             (!FLGI :SF 0
                    (!FLGI :OF
                           (OF-SPEC32 (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
                           X86))))))))))
     (SEM-16
      (XW
       :RGF *RAX*
       (LOGHEAD 32
                (* (LOGEXT 32 (XR :RGF *RAX* X86))
                   (LOGEXT 32 (XR :RGF *RDI* X86))))
       (XW
        :RGF *RDI*
        (LOGHEAD 32
                 (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
        (XW
         :RIP nil 16
         (XW
          :UNDEF nil (+ 4 (NFIX (XR :UNDEF nil X86)))
          (!FLGI
           :CF
           (LOGHEAD 1
                    (BOOL->BIT (< (LOGHEAD 32 (XR :RGF *RDI* X86)) 1)))
           (!FLGI
            :PF
            (PF-SPEC32 (LOGHEAD 32
                                (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86)))))
            (!FLGI
             :AF
             (SUB-AF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86))
                            1)
             (!FLGI
              :ZF 0
              (!FLGI
               :SF
               (SF-SPEC32 (LOGHEAD 32
                                   (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86)))))
               (!FLGI :OF
                      (OF-SPEC32 (+ -1 (LOGEXT 32 (XR :RGF *RDI* X86))))
                      X86))))))))))))
    X86))

 (ACL2::DEFUNM-NX
  SEM-0 (X86)
  (DECLARE (XARGS :STOBJS (X86)))
  (IF
   (FACTORIAL-HYPS X86)
   (IF
    (EQUAL (LOGHEAD 32 (XR :RGF *RDI* X86))
           0)
    (XW
     :RGF *RAX* 1
     (XW
      :RIP nil 24
      (XW
       :UNDEF nil (+ 1 (NFIX (XR :UNDEF nil X86)))
       (!FLGI :CF 0
              (!FLGI :PF 1
                     (!FLGI :AF
                            (LOGHEAD 1
                                     (CREATE-UNDEF (NFIX (XR :UNDEF nil X86))))
                            (!FLGI :ZF 1
                                   (!FLGI :SF 0 (!FLGI :OF 0 X86)))))))))
    (SEM-16
     (XW
      :RGF *RAX* 1
      (XW
       :RIP nil 16
       (XW
        :UNDEF nil (+ 1 (NFIX (XR :UNDEF nil X86)))
        (!FLGI
         :CF 0
         (!FLGI
          :PF
          (PF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86)))
          (!FLGI :AF
                 (LOGHEAD 1
                          (CREATE-UNDEF (NFIX (XR :UNDEF nil X86))))
                 (!FLGI :ZF 0
                        (!FLGI :SF
                               (SF-SPEC32 (LOGHEAD 32 (XR :RGF *RDI* X86)))
                               (!FLGI :OF 0 X86)))))))))))
   X86))

 ;; (acl2::why x86-run-opener-not-ms-not-zp-n)
 ;; (acl2::why x86-fetch-decode-execute-opener)
 ;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
 ;; (acl2::why one-read-with-rb-from-program-at)
 ;; (acl2::why program-at-wb-disjoint)

 (DEFTHM SEM-16-CORRECT
   (IMPLIES (AND (FACTORIAL-HYPS X86)
                 (EQUAL (XR :RIP nil X86) 16))
            (EQUAL (X86-RUN-ALT X86 (CLK-16 X86))
                   (SEM-16 X86))))

 (IN-THEORY (DISABLE CLK-16))

 (DEFTHM SEM-0-CORRECT
   (IMPLIES (AND (FACTORIAL-HYPS X86)
                 (EQUAL (XR :RIP nil X86) 0))
            (EQUAL (X86-RUN-ALT X86 (CLK-0 X86))
                   (SEM-0 X86))))

 (IN-THEORY (DISABLE CLK-0)))

;; ======================================================================

;; Relating the program and the specification:

(encapsulate
  ()
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

  (defun fact-algorithm (n a)
    (if (posp n)
        (let* ((a (n32 (* (n32-to-i32 a) (n32-to-i32 n))))
               (n (n32 (- (n32-to-i32 n) 1))))
          (if (not (equal n 0))
              (fact-algorithm n a)
            a))
      1)))

(defthm factorial-loop-result-helper
  (implies (and (factorial-hyps x86)
                (equal (xr :rip nil x86) 16)
                (< 0 (rgfi *rdi* x86))
                (< 0 (rgfi *rax* x86)))
           (equal (xr :rgf *rax* (sem-16 x86))
                  (fact-algorithm (rgfi *rdi* x86) (rgfi *rax* x86)))))

(defthm factorial-program-result-helper
  (implies (and (factorial-hyps x86)
                (equal (xr :rip nil x86) 0))
           (equal (xr :rgf *rax* (sem-0 x86))
                  (fact-algorithm (rgfi *rdi* x86) 1)))
  :hints (("Goal" :in-theory (e/d* () ()))))

(defun f (n)
  (if (zp n)
      1
    (* n (f (- n 1)))))

(defun fact-algorithm-simple (n a)
  (if (posp n)
      (let* ((a (* a n))
             (n (- n 1)))
        (if (not (equal n 0))
            (fact-algorithm-simple n a)
          a))
    1))

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

(defthm factorial-program-result
  (implies (and (factorial-hyps x86)
                (equal (xr :rip nil x86) 0))
           (equal (xr :rgf *rax* (x86-run-alt x86 (clk-0 x86)))
                  (f (rgfi *rdi* x86)))))

;; ----------------------------------------------------------------------
