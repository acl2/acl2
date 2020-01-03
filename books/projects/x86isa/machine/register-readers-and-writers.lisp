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
(include-book "rflags-spec")
(include-book "fp-structures" :dir :utils)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
; Instruction to cert.pl for dependency tracking.
; (depends-on "register-readers-and-writers-raw.lsp")

;; ======================================================================

(defsection register-readers-and-writers
  :parents (machine)
  :short "Top-level utilities for reading and writing into various
  registers"
  )

;; ======================================================================

(defsection GPR-indices

  :parents (register-readers-and-writers)

  :short "Functions that enable the use of extended GPRs using the
  @('rex') byte"

  (local (xdoc::set-default-parents GPR-indices))

  (define reg-indexp
    ((reg)
     (rex-byte :type (unsigned-byte 8)))
    :short "Valid GPR index recognizer"
    :long "<p>General-purpose register indices are 3 bits except in
64-bit mode, where they can have 4 bits depending on the @('rex')
prefix.</p>"
    :enabled t
    (if (eql rex-byte 0)
        (n03p reg)
      (n04p reg))

    ///

    (defthm reg-indexp-for-3-bits
      (implies (and (syntaxp (quotep reg))
                    (n03p reg))
               (reg-indexp reg rex)))

    (defthm reg-indexp-logand-7
      (implies (n08p rex-byte)
               (reg-indexp (loghead 3 modr/m) rex-byte))
      :hints (("Goal" :in-theory (enable reg-indexp)))))

  (define reg-index
    ((reg      :type (unsigned-byte 3) "Register index")
     (rex-byte :type (unsigned-byte 8) "REX prefix")
     (index    :type (unsigned-byte 2) "One of the W, R, X, or B bits of the REX prefix"))
    :inline t
    :no-function t
    :short "Using the REX prefix to access general-purpose registers"
    :long "<p>In 64-bit mode, in addition to generating 64-bit operand sizes,
    the REX prefix is used to reference registers R8 to R15. Instructions that
    include REX prefixes can access these registers if the relevant W, R, X, or
    B bit in the REX prefix is set. E.g., let R be the relevant bit in the REX
    prefix and let R be set --- so @('index') = @(`*r*`) for this function. If
    @('reg') = 0 (which, in the non-REX world, would refer to rAX),
    @('reg-index') would give us the register index corresponding to the
    register r8. If R is not set, @('reg-index') will give us the index
    corresponding to rAX.</p>

    <p>In 32-bit mode, the REX prefix is absent.  This function can be used in
    32-bit mode, by passing 0 as REX.</p>"

    (if (logbitp index rex-byte)
        (logior 8 (mbe :logic (n03 reg) :exec reg))
      (mbe :logic (n03 reg) :exec reg))

    ///

    (local (in-theory (e/d (reg-indexp) ())))

    (defthm reg-indexp-reg-index
      (reg-indexp (reg-index reg rex-byte name) rex-byte))

    (defthm-unsigned-byte-p n04p-reg-index
      :hyp t
      :bound 4
      :concl (reg-index reg rex-byte name)
      :gen-linear t
      :gen-type t)

    (defthm reg-indexp-forward
      (implies (reg-indexp reg rex-byte)
               (unsigned-byte-p 4 reg))
      :rule-classes :forward-chaining)))

;; ======================================================================

;; [Jared] these rules broke something below
(local (in-theory (disable BITOPS::LOGEXT-OF-LOGAND
                           BITOPS::LOGEXT-OF-LOGIOR)))

(defsection GPRs-Reads-and-Writes

  :parents (register-readers-and-writers)

  :short "Functions to read/write 8/16/32/64 bits into the registers"

  :long "<p>@(see rr08), @(see rr16), @(see rr32), and @(see rr64)
will read the contents of the GPRs as natural numbers. Remember that
@('rgfi') will return an @(see i64p) value.</p>

<p>Here is an example:</p>
<br/>
<tt>
\(!rgfi 0 -1 x86\) ;; Write -1 to register 0
</tt>

<p><tt>\(rr64 0 x86\)</tt> returns @('18446744073709551615') and
<tt>(rgfi 0 x86)</tt> returns @('-1').  Note that
@('18446744073709551615') is a bignum in CCL. This is precisely the
reason why we declared registers as @('i64p') instead of @('n64p');
@('-1') would be stored as a bignum if the registers were
@('n64p'). </p>

<p>Similarly, @(see wr08), @(see wr16), @(see wr32), and @(see wr64)
are used to write natural numbers into the GPRs.</p>"

  (local (xdoc::set-default-parents GPRs-Reads-and-Writes))

  (define rr08
    ((reg :type (unsigned-byte 4))
     (rex :type (unsigned-byte 8))
     (x86))
    :inline t
    :no-function t
    :guard (reg-indexp reg rex)
    :short "Read from byte general-purpose registers"
    :long "<p><i>Source: Intel Manuals, Vol. 1, Section
    3.4.1.1 (General-Purpose Registers in 64-bit Mode)</i></p>

 <blockquote>In 64-bit mode, there are limitations on accessing byte
 registers. An instruction cannot reference legacy high-bytes (for example: AH,
 BH, CH, DH) and one of the new byte registers at the same time (for example:
 the low byte of the RAX register). However, instructions may reference legacy
 low-bytes (for example: AL, BL, CL or DL) and new byte registers at the same
 time (for example: the low byte of the R8 register, or R8L). The architecture
 enforces this limitation by changing high-byte references (AH, BH, CH, DH) to
 low byte references (BPL, SPL, DIL, SIL: the low 8 bits for RBP, RSP, RDI and
 RSI) for instructions using a REX prefix.</blockquote>

 <p>In other words, without the REX prefix, indices 0-7 refer to byte registers
 AL, CL, DL, BL, AH, CH, DH, and BH, whereas with the REX prefix, indices 0-15
 refer to AL, CL, DL, BL, SPL, BPL, SIL, DIL, R8L, R9L, R10L, R11L, R12L, R13L,
 R14L, R15L. This applies to 64-bit mode.</p>

 <p>In 32-bit mode, this function is called with 0 as REX.</p>"

    (cond ((or (not (eql rex 0))
               (< reg 4))
           (let ((qword (the (signed-byte 64) (rgfi reg x86))))
             (n08 qword)))
          (t ;; no rex and reg is at least 4 -- then read from AH, etc.
           (let ((qword
                  (the (signed-byte 64) (rgfi (the (unsigned-byte 4) (- reg 4)) x86))))
             (mbe :logic (part-select qword :low 8 :width 8)
                  :exec (n08 (ash qword -8))))))

    ///

    (defthm-unsigned-byte-p n08p-rr08
      :hyp t
      :bound 8
      :concl (rr08 reg rex x86)
      :gen-linear t
      :gen-type t))

  (define rr16
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :short "Read from word general-purpose registers"

    (n16 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-unsigned-byte-p n16p-rr16
      :hyp t
      :bound 16
      :concl (rr16 reg x86)
      :gen-linear t
      :gen-type t))

  (define rr32
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :short "Read from doubleword general-purpose registers"

    (n32 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-unsigned-byte-p n32p-rr32
      :hyp t
      :bound 32
      :concl (rr32 reg x86)
      :gen-linear t
      :gen-type t))

  (define rr64
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :short "Read from quadword general-purpose registers"
    :long "<p>This function is used only in 64-bit mode.</p>"

    (n64 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-unsigned-byte-p n64p-rr64
      :hyp t
      :bound 64
      :concl (rr64 reg x86)
      :gen-linear t
      :gen-type t))

  (define wr08
    ((reg  :type (unsigned-byte 4))
     (rex  :type (unsigned-byte 8))
     (byte :type (unsigned-byte 8))
     (x86))
    :inline t
    :no-function t
    :guard (reg-indexp reg rex)
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    :short "Writing to byte general-purpose registers"
    :long "<p>Note Intel Vol. 1 Sec. 3.4.1.1
    p. 3-17, which says the following about 64-bit mode:</p>

    <p><em>8-bit and 16-bit operands generate an 8-bit or 16-bit result.
    The upper 56 or 48 bits (respectively) of the destination general-purpose
    register are not modified by the operation.</em></p>

    <p>This is also confirmed by AMD manual, Jun'15, Vol. 3, App. B.1, under
    &lsquo;No Extension of 8-Bit and 16-Bit Results&rsquo;.</p>

    <p>In 32-bit mode, the upper 32 bits are undefined, as specified by
    the following quote from the same page as above:</p>

    <p><em>Because the upper 32 bits of 64-bit general-purpose registers are
    undefined in 32-bit modes, the upper 32 bits of any general-purpose
    register are not preserved when switching from 64-bit mode to a 32-bit
    mode (to protected mode or compatibility mode). Software must not depend on
    these bits to maintain a value after a 64-bit to 32-bit mode
    switch.</em></p>

    <p>In 32-bit mode, this function is called with 0 as REX.  Since in 32-bit
    mode the high 32 bits of general-purpose registers are not accessible, it
    is fine for this function to leave those bits unchanged, as opposed to, for
    example, setting them to undefined values as done by the semantic functions
    of certain instructions for certain flags. The switching from 32-bit mode
    to 64-bit mode (when modeled) will set the high 32 bits of general-purpose
    registers to undefined values.</p>"


    (cond ((or (not (eql rex 0))
               (< reg 4))
           (let ((qword (the (signed-byte 64) (rgfi reg x86))))
             (!rgfi reg
                    (n64-to-i64
                     (mbe :logic
                          (part-install
                           byte
                           (part-select qword :low 0 :width 64)
                           :low 0 :width 8)
                          :exec
                          (the (unsigned-byte 64)
                            (logior (the (unsigned-byte 64)
                                      (logand #xffffffffffffff00 qword))
                                    byte))))
                    x86)))
          (t ;; no rex and reg is at least 4 -- then write to AH, etc.
           (let* ((index (the (unsigned-byte 4)
                           (- (the (unsigned-byte 4) reg) 4)))
                  (qword (the (signed-byte 64) (rgfi index x86))))
             (!rgfi index
                    (n64-to-i64
                     (mbe :logic
                          (part-install
                           byte
                           (part-select qword :low 0 :width 64)
                           :low 8 :width 8)
                          :exec
                          (the (unsigned-byte 64)
                            (logior (the (unsigned-byte 64)
                                      (logand #xffffffffffff00ff qword))
                                    (the (unsigned-byte 16) (ash byte 8))))))
                    x86))))

    ///

    (defthm x86p-wr08
      (implies (x86p x86)
               (x86p (wr08 reg rex byte x86)))))

  (encapsulate
    ()

    (local
     (include-book "arithmetic-5/top" :dir :system))

    (defthm loghead-logtail-logext-for-rr08/wr08
      (implies (integerp x)
               (equal (loghead 8 (logtail 8 (logext 64 x)))
                      (loghead 8 (logtail 8 x))))
      :hints (("Goal" :in-theory
               (e/d (logtail evenp oddp logbitp logext loghead logapp)
                    ())))))

  (defthm rr08-wr08-same
    (equal (rr08 reg rex (wr08 reg rex byte x86))
           (loghead 8 byte))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr08 wr08)
                             (unsigned-byte-p
                              (force) force)))))

  (defthm rr08-wr08-different
    (implies (not (equal reg1 reg2))
             (equal (rr08 reg1 rex1 (wr08 reg2 rex2 byte x86))
                    (rr08 reg1 rex1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr08 wr08)
                             (force (force))))))

  (define wr16
    ((reg  :type (unsigned-byte 4))
     (val  :type (unsigned-byte 16))
     (x86))
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    :short "Write to word general-purpose registers"
    :long "<p>Note Intel Vol. 1 Sec. 3.4.1.1
    p. 3-17, which says the following about 64-bit mode:</p>

    <p><em>8-bit and 16-bit operands generate an 8-bit or 16-bit result.
    The upper 56 or 48 bits (respectively) of the destination general-purpose
    register are not modified by the operation.</em></p>

    <p>This is also confirmed by AMD manual, Jun'15, Vol. 3, App. B.1, under
    &lsquo;No Extension of 8-Bit and 16-Bit Results&rsquo;.</p>

    <p>In 32-bit mode, the upper 32 bits are undefined, as specified by
    the following quote from the same page as above:</p>

    <p><em>Because the upper 32 bits of 64-bit general-purpose registers are
    undefined in 32-bit modes, the upper 32 bits of any general-purpose
    register are not preserved when switching from 64-bit mode to a 32-bit
    mode (to protected mode or compatibility mode). Software must not depend on
    these bits to maintain a value after a 64-bit to 32-bit mode
    switch.</em></p>

    <p>This function is used both in 64-bit mode and in 32-bit mode. Since in
    32-bit mode the high 32 bits of general-purpose registers are not
    accessible, it is fine for this function to leave those bits unchanged, as
    opposed to, for example, setting them to undefined values as done by the
    semantic functions of certain instructions for certain flags. The switching
    from 32-bit mode to 64-bit mode (when modeled) will set the high 32 bits of
    general-purpose registers to undefined values.</p>"

    (let ((qword (the (signed-byte 64) (rgfi reg x86))))
      (!rgfi reg
             (n64-to-i64
              (mbe :logic
                   (part-install
                    val
                    (part-select qword :low 0 :width 64)
                    :low 0 :width 16)
                   :exec
                   (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 64)
                               (logand qword #xffffffffffff0000))
                             val))))
             x86))

    ///

    (defthm x86p-wr16
      (implies (x86p x86)
               (x86p (wr16 reg val x86)))))

  (defthm rr16-wr16-same
    (equal (rr16 reg (wr16 reg val x86))
           (loghead 16 val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr16 wr16)
                             (unsigned-byte-p force (force))))))

  (defthm rr16-wr16-different
    (implies (not (equal reg1 reg2))
             (equal (rr16 reg1 (wr16 reg2 val x86))
                    (rr16 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr16 wr16)
                             (force (force))))))

  (define wr32
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 32))
     (x86))
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    :short "Write to doubleword general-purpose registers"
    :long "<p>Note Intel Vol. 1 Sec. 3.4.1.1
    p. 3-17, which says the following about 64-bit mode:</p>

    <p><em>32-bit operands generate a 32-bit result, zero-extended to a
    64-bit result in the destination general-purpose
    register.</em></p>

    <p>This is also confirmed by AMD manual, Jun'15, Vol. 3, App. B.1, under
    `No Extension of 8-Bit and 16-Bit Results'.</p>

    <p>In 32-bit mode, the upper 32 bits are undefined, as specified by the
    following quote from the same page as above:</p>

    <p><em>Because the upper 32 bits of 64-bit general-purpose registers are
    undefined in 32-bit modes, the upper 32 bits of any general-purpose
    register are not preserved when switching from 64-bit mode to a 32-bit
    mode (to protected mode or compatibility mode). Software must not depend on
    these bits to maintain a value after a 64-bit to 32-bit mode
    switch.</em></p>

    <p>This function is used both in 64-bit mode and in 32-bit mode. Since in
    32-bit mode the high 32 bits of general-purpose registers are not
    accessible, it is fine for this function to set those bits to 0, as opposed
    to, for example, setting them to undefined values as done by the semantic
    functions of certain instructions for certain flags. The switching from
    32-bit mode to 64-bit mode (when modeled) will set the high 32 bits of
    general-purpose registers to undefined values.</p>"

    (!rgfi reg (mbe :logic (n32 val) :exec val) x86)

    ///

    (defthm x86p-wr32
      (implies (x86p x86)
               (x86p (wr32 reg val x86)))))

  (defthm rr32-wr32-same
    (equal (rr32 reg (wr32 reg val x86))
           (loghead 32 val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr32 wr32)
                             (unsigned-byte-p)))))

  (defthm rr32-wr32-different
    (implies (not (equal reg1 reg2))
             (equal (rr32 reg1 (wr32 reg2 val x86))
                    (rr32 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr32 wr32)
                             ()))))

  (define wr64
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 64))
     (x86))
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    (!rgfi reg (n64-to-i64 val) x86)
    :short "Write to quadword general-purpose registers"
    :long "<p>This function is used only in 64-bit mode.</p>"

    ///
    (defthm x86p-wr64
      (implies (x86p x86)
               (x86p (wr64 reg val x86)))))

  (defthm rr64-wr64-same
    (equal (rr64 reg (wr64 reg val x86))
           (loghead 64 val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr64 wr64)
                             (unsigned-byte-p)))))

  (defthm rr64-wr64-different
    (implies (not (equal reg1 reg2))
             (equal (rr64 reg1 (wr64 reg2 val x86))
                    (rr64 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr64 wr64)
                             ()))))

  (define rgfi-size
    ((nbytes :type (unsigned-byte 4))
     (index  :type (unsigned-byte 4))
     (rex    :type (unsigned-byte 8))
     x86)
    :enabled t
    :guard (and (reg-indexp index rex)
                (member nbytes '(1 2 4 8)))
    :inline t
    :no-function t
    :returns (val natp :rule-classes :type-prescription)
    :short "Read form byte, word, doubleword, or quadword
            general-purpose register"
    (case nbytes
      (1 (rr08 index rex x86))
      (2 (rr16 index x86))
      (4 (rr32 index x86))
      (8 (rr64 index x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 1, 2, 4, or 8.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       0)))


  (define !rgfi-size
    ((nbytes :type (unsigned-byte 4))
     (index  :type (unsigned-byte 4))
     (val    :type integer)
     (rex    :type (unsigned-byte 8))
     x86)
    :enabled t
    :guard (and (reg-indexp index rex)
                (member nbytes '(1 2 4 8))
                (unsigned-byte-p (ash nbytes 3) val))
    :returns (x86 x86p :hyp (x86p x86))
    :inline t
    :no-function t
    :short "Write to byte, word, doubleword, or quadword
            general-purpose register"
    (case nbytes
      (1 (wr08 index rex val x86))
      (2 (wr16 index val x86))
      (4 (wr32 index val x86))
      (8 (wr64 index val x86))
      (otherwise
       ;; The guard says nbytes shouldn't be anything other than 1, 2,
       ;; 4, or 8.
       x86))))

;; ======================================================================

(defsection MMX-Registers-Reads-and-Writes

  :parents (register-readers-and-writers)

  :short "Functions to read/write into the MMX registers"

  :long "<p>From Section 12.2, Intel Manual, Volume 3 \(System
  Programming\):</p>

  <p><em>The MMX state consists of eight 64-bit registers \(MM0
through MM7\). These registers are aliased to the low 64-bits \(bits 0
through 63\) of floating-point registers R0 through R7 \(see Figure
12-1\). Note that the MMX registers are mapped to the physical
locations of the floating-point registers \(R0 through R7\), not to
the relative locations of the registers in the floating-point register
stack \(ST0 through ST7\). As a result, the MMX register mapping is
fixed and is not affected by value in the Top Of Stack \(TOS\) field
in the floating-point status word \(bits 11 through 13\).</em></p>

<p>From Section 12.2, Intel Manual, Volume 3 \(System Programming\)</p>:

<p><em>When a value is written into an MMX register using an MMX
instruction, the value also appears in the corresponding
floating-point register in bits 0 through 63. Likewise, when a
floating-point value written into a floating-point register by a x87
FPU, the low 64 bits of that value also appears in a the corresponding
MMX register.</em></p>

<p><em>The execution of MMX instructions have several side effects on
the x87 FPU state contained in the floating-point registers, the x87
FPU tag word, and the x87 FPU status word. These side effects are as
follows:</em></p>

<p><em>* When an MMX instruction writes a value into an MMX register,
at the same time, bits 64 through 79 of the corresponding
floating-point register are set to all 1s.</em></p>

<p><em>* When an MMX instruction \(other than the EMMS instruction\) is
executed, each of the tag fields in the x87 FPU tag word is set to 00B
\(valid\). \(See also Section 12.2.1, Effect of MMX, x87 FPU, FXSAVE,
and FXRSTOR Instructions on the x87 FPU Tag Word.\)</em></p>

<p><em>* When the EMMS instruction is executed, each tag field in the
x87 FPU tag word is set to 11B \(empty)\.</em></p>

<p><em>* Each time an MMX instruction is executed, the TOS value is
set to 000B.  Execution of MMX instructions does not affect the other
bits in the x87 FPU status word \(bits 0 through 10 and bits 14 and
15\) or the contents of the other x87 FPU registers that comprise the
x87 FPU state \(the x87 FPU control word, instruction pointer, data
pointer, or opcode registers\).</em></p>"

  (local (xdoc::set-default-parents MMX-Registers-Reads-and-Writes))

  (define mmx
    ((i :type (integer 0 7))
     (x86))
    :inline t
    :no-function t
    (let ((reg80 (the (unsigned-byte 80) (fp-datai i x86))))
      (mbe :logic (part-select reg80 :low 0 :width 64)
           :exec  (logand #.*2^64-1* reg80)))

    ///

    (defthm-unsigned-byte-p n64p-mmx
      :hyp t
      :bound 64
      :concl (mmx i x86)
      :gen-type t
      :gen-linear t))

  (define !mmx
    ((i :type (integer      0 7))
     (v :type (unsigned-byte 64))
     (x86))
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p))))

    (let ((val80 (mbe :logic (part-install #xFFFF v :low 64 :high 79)
                      :exec (the (unsigned-byte 80)
                              (logior #uxFFFF_00000000_00000000 v)))))
      (!fp-datai i val80 x86))

    ///

    (defthm x86p-!mmx
      (implies (x86p x86)
               (x86p (!mmx i v x86)))
      :hints (("Goal" :in-theory (e/d () (force (force)))))))

  (define mmx-instruction-updates (x86)
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d ()
                                          ())))
    :short "We set the FPU tag and TOS field to 00B \(valid\) and 000B
 respectively.  This function accounts for the effects of all MMX
 instructions except EMMS."

    (b* ((x86 (!fp-tag 0 x86))
         (fp-status (fp-status x86))
         (x86 (!fp-status (!fp-statusBits->top 0 fp-status) x86)))
        x86)

    ///

    (defthm x86p-mmx-instruction-updates
      (implies (x86p x86)
               (x86p (mmx-instruction-updates x86))))))

;; ======================================================================

(defsection ZMMs-Reads-and-Writes

  :parents (register-readers-and-writers)

  :short "Functions to read/write 32/64/128/256/512 bits into the
  XMM/YMM/ZMM registers"

  :long "<p>Source: Intel Vol. 1, Section 15.5: ACCESSING XMM, YMM AND ZMM
 REGISTERS</p>

 <blockquote>The lower 128 bits of a YMM register is aliased to the
 corresponding XMM register. Legacy SSE instructions (i.e., SIMD
 instructions operating on XMM state but not using the VEX prefix,
 also referred to non-VEX encoded SIMD instructions) will not access
 the upper bits (MAXVL-1:128) of the YMM registers. AVX and FMA
 instructions with a VEX prefix and vector length of 128-bits zeroes
 the upper 128 bits of the YMM register.</blockquote>

 <blockquote>Upper bits of YMM registers (255:128) can be read and
 written to by many instructions with a VEX.256 prefix. XSAVE and
 XRSTOR may be used to save and restore the upper bits of the YMM
 registers.</blockquote>

 <blockquote>The lower 256 bits of a ZMM register are aliased to the
 corresponding YMM register. Legacy SSE instructions (i.e., SIMD
 instructions operating on XMM state but not using the VEX prefix,
 also referred to non-VEX encoded SIMD instructions) will not access
 the upper bits (MAXVL-1:128) of the ZMM registers, where MAXVL is
 maximum vector length (currently 512 bits). AVX and FMA instructions
 with a VEX prefix and vector length of 128-bits zero the upper 384
 bits of the ZMM register, while the VEX prefix and vector length of
 256-bits zeroes the upper 256 bits of the ZMM register.  Upper bits
 of ZMM registers (511:256) can be read and written to by instructions
 with an EVEX.512 prefix.</blockquote>

 <p>@(see rz32), @(see rz64), @(see rz128), @(see rz256), and @(see
 rz512) will read the contents of the ZMMs as natural numbers.</p>

 <p>Similarly, @(see wz32), @(see wz64), @(see wz128), @(see wz256),
 and @(see wz512) are used to write natural numbers into the
 ZMMs.</p>"

  (local (xdoc::set-default-parents ZMMs-Reads-and-Writes))

  (define rz32
    ((reg :type (unsigned-byte 5))
     (x86))
    :inline t
    :no-function t

    (n32 (the (unsigned-byte 512) (zmmi reg x86)))

    ///

    (defthm-unsigned-byte-p n32p-rz32
      :hyp t
      :bound 32
      :concl (rz32 reg x86)
      :gen-linear t
      :gen-type t))

  (define rz64
    ((reg :type (unsigned-byte 5))
     (x86))
    :inline t
    :no-function t

    (n64 (the (unsigned-byte 512) (zmmi reg x86)))

    ///

    (defthm-unsigned-byte-p n64p-rz64
      :hyp t
      :bound 64
      :concl (rz64 reg x86)
      :gen-linear t
      :gen-type t))

  (define rz128
    ((reg :type (unsigned-byte 5))
     (x86))
    :inline t
    :no-function t

    (n128 (the (unsigned-byte 512) (zmmi reg x86)))

    ///

    (defthm-unsigned-byte-p n128p-rz128
      :hyp t
      :bound 128
      :concl (rz128 reg x86)
      :gen-linear t
      :gen-type t))

  (define rz256
    ((reg :type (unsigned-byte 5))
     (x86))
    :inline t
    :no-function t

    (n256 (the (unsigned-byte 512) (zmmi reg x86)))

    ///

    (defthm-unsigned-byte-p n256p-rz256
      :hyp t
      :bound 256
      :concl (rz256 reg x86)
      :gen-linear t
      :gen-type t))

  (define rz512
    ((reg :type (unsigned-byte 5))
     (x86))
    :inline t
    :no-function t

    (n512 (the (unsigned-byte 512) (zmmi reg x86)))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm-unsigned-byte-p n512p-rz512
      :hyp t
      :bound 512
      :concl (rz512 reg x86)
      :gen-linear t
      :gen-type t))

  (define vector-access-type-p (x)
    :returns (ok? booleanp :rule-classes :type-prescription)
    :enabled t
    (or (equal x #.*xmm-access*)
        (equal x #.*vex-xmm-access*)
        (equal x #.*ymm-access*)
        (equal x #.*zmm-access*)))

  (define wz32
    ((reg  :type (unsigned-byte  5))
     (val  :type (unsigned-byte 32))
     (x86)
     &key
     ((regtype vector-access-type-p) '*zmm-access*))
    :short "Write @('val') to low 32 bits of a ZMM register"
    :long "<p><i>Upper bits</i>: For XMM registers, upper @(`(- 512
     128)`) bits are preserved if @('regtype') is @('*xmm-access*');
     for @('*vex-xmm-access*'), these bits are zeroed out.  For
     @('*ymm-access*'), upper @(`(- 512 256)`) bits are zeroed
     out. For @('*zmm-access*'), no upper bits are zeroed out.</p>"
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (b* ((data (the (unsigned-byte 512) (zmmi reg x86)))
         (regtype (the (unsigned-byte 3) regtype))
         (data (case regtype
                 (#.*vex-xmm-access*
                  (loghead 128 data))
                 (#.*ymm-access*
                  (loghead 256 data))
                 (otherwise
                  ;; Preserve upper bits.
                  data)))
         (val  (n32 (the (unsigned-byte 32) val))))
      (!zmmi reg (part-install val data :low 0 :width 32) x86))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm x86p-wz32
      (implies (x86p x86)
               (x86p (wz32 reg val x86 :regtype access)))))

  (defthm rz32-wz32-same
    (equal (rz32 reg (wz32 reg val x86 :regtype access))
           (loghead 32 val))
    :hints (("Goal"
             :in-theory (e/d (rz32 wz32)
                             (unsigned-byte-p
                              force (force))))))

  (defthm rz32-wz32-different
    (implies (not (equal reg1 reg2))
             (equal (rz32 reg1 (wz32 reg2 val x86 :regtype access))
                    (rz32 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rz32 wz32)
                             (force (force))))))

  (define wz64
    ((reg  :type (unsigned-byte  5))
     (val  :type (unsigned-byte 64))
     (x86)
     &key
     ((regtype vector-access-type-p) '*zmm-access*))
    :short "Write @('val') to low 64 bits of a ZMM register"
    :long "<p><i>Upper bits</i>: For XMM registers, upper @(`(- 512
     128)`) bits are preserved if @('regtype') is @('*xmm-access*');
     for @('*vex-xmm-access*'), these bits are zeroed out.  For
     @('*ymm-access*'), upper @(`(- 512 256)`) bits are zeroed
     out. For @('*zmm-access*'), no upper bits are zeroed out.</p>"
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    (b* ((data (the (unsigned-byte 512) (zmmi reg x86)))
         (regtype (the (unsigned-byte 3) regtype))
         (data (case regtype
                 (#.*vex-xmm-access*
                  (loghead 128 data))
                 (#.*ymm-access*
                  (loghead 256 data))
                 (otherwise
                  ;; Preserve upper bits.
                  data)))
         (val  (the (unsigned-byte 64) (n64 val))))
      (!zmmi reg (part-install val data :low 0 :width 64) x86))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm x86p-wz64
      (implies (x86p x86)
               (x86p (wz64 reg val x86 :regtype access)))))

  (defthm rz64-wz64-same
    (equal (rz64 reg (wz64 reg val x86 :regtype access))
           (loghead 64 val))
    :hints (("Goal"
             :in-theory (e/d (rz64 wz64)
                             (unsigned-byte-p
                              force (force))))))

  (defthm rz64-wz64-different
    (implies (not (equal reg1 reg2))
             (equal (rz64 reg1 (wz64 reg2 val x86 :regtype access))
                    (rz64 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rz64 wz64)
                             (force (force))))))

  (define wz128
    ((reg  :type (unsigned-byte 5))
     (val  :type (unsigned-byte 128))
     (x86)
     &key
     ((regtype vector-access-type-p) '*zmm-access*))
    :short "Write @('val') to low 128 bits of a ZMM register"
    :long "<p><i>Upper bits</i>: For XMM registers, upper @(`(- 512
     128)`) bits are preserved if @('regtype') is @('*xmm-access*');
     for @('*vex-xmm-access*'), these bits are zeroed out.  For
     @('*ymm-access*'), upper @(`(- 512 256)`) bits are zeroed
     out. For @('*zmm-access*'), no upper bits are zeroed out.</p>"
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (b* ((data (the (unsigned-byte 512) (zmmi reg x86)))
         (regtype (the (unsigned-byte 3) regtype))
         (data (case regtype
                 (#.*vex-xmm-access*
                  (loghead 128 data))
                 (#.*ymm-access*
                  (loghead 256 data))
                 (otherwise
                  ;; Preserve upper bits.
                  data)))
         (val (the (unsigned-byte 128) (n128 val))))
      (!zmmi reg (part-install val data :low 0 :width 128) x86))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm x86p-wz128
      (implies (x86p x86)
               (x86p (wz128 reg val x86 :regtype access)))))

  (defthm rz128-wz128-same
    (equal (rz128 reg (wz128 reg val x86 :regtype access))
           (loghead 128 val))
    :hints (("Goal"
             :in-theory (e/d (rz128 wz128)
                             (unsigned-byte-p
                              force (force))))))

  (defthm rz128-wz128-different
    (implies (not (equal reg1 reg2))
             (equal (rz128 reg1 (wz128 reg2 val x86 :regtype access))
                    (rz128 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rz128 wz128)
                             (force (force))))))

  (define wz256
    ((reg  :type (unsigned-byte 5))
     (val  :type (unsigned-byte 256))
     (x86)
     &key
     ((regtype vector-access-type-p) '*zmm-access*))

    :short "Write @('val') to low 256 bits of a ZMM register."
    :long "<p><i>Upper bits</i>: For @('*ymm-access*'), upper @(`(-
     512 256)`) bits are zeroed out. For @('*zmm-access*'), no upper
     bits are zeroed out.</p>"
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (b* ((data (the (unsigned-byte 512) (zmmi reg x86)))
         (regtype (the (unsigned-byte 3) regtype))
         (data (case regtype
                 (#.*ymm-access*
                  (loghead 256 data))
                 (otherwise
                  ;; Preserve upper bits.
                  data)))
         (val (the (unsigned-byte 256) (n256 val))))
      (!zmmi reg (part-install val data :low 0 :width 256) x86))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm x86p-wz256
      (implies (x86p x86)
               (x86p (wz256 reg val x86 :regtype access)))))

  (defthm rz256-wz256-same
    (equal (rz256 reg (wz256 reg val x86 :regtype access))
           (loghead 256 val))
    :hints (("Goal"
             :in-theory (e/d (rz256 wz256)
                             (unsigned-byte-p
                              force (force))))))

  (defthm rz256-wz256-different
    (implies (not (equal reg1 reg2))
             (equal (rz256 reg1 (wz256 reg2 val x86 :regtype access))
                    (rz256 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rz256 wz256)
                             (force (force))))))

  (define wz512
    ((reg  :type (unsigned-byte 5))
     (val  :type (unsigned-byte 512))
     (x86))
    :short "Write @('val') to 512 bits of a ZMM register."
    :inline t
    :no-function t
    :guard-hints (("Goal" :in-theory (e/d (loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (let ((val (the (unsigned-byte 512) (n512 val))))
      (!zmmi reg val x86))

    ///

    (local (in-theory (e/d () (force (force)))))

    (defthm x86p-wz512
      (implies (x86p x86)
               (x86p (wz512 reg val x86)))))

  (defthm rz512-wz512-same
    (equal (rz512 reg (wz512 reg val x86))
           (loghead 512 val))
    :hints (("Goal"
             :in-theory (e/d (rz512 wz512)
                             (unsigned-byte-p
                              force (force))))))

  (defthm rz512-wz512-different
    (implies (not (equal reg1 reg2))
             (equal (rz512 reg1 (wz512 reg2 val x86))
                    (rz512 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rz512 wz512)
                             (force (force))))))

  (define zmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 5))
     x86)
    :enabled t
    :guard (member nbytes '(4 8 16 32 64))
    :inline t
    :no-function t
    :returns (val natp :rule-classes :type-prescription)
    (case nbytes
      (4  (rz32  index x86))
      (8  (rz64  index x86))
      (16 (rz128 index x86))
      (32 (rz256 index x86))
      (64 (rz512 index x86))
      (otherwise
       0)))

  (define !zmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 5))
     (val    :type integer)
     x86
     &key
     ((regtype vector-access-type-p) '*zmm-access*))
    :short "Write @('val') to low @('nbytes') of a ZMM register"
    :long "<p><i>Upper bits</i>: For XMM registers, upper @(`(- 512
     128)`) bits are preserved if @('regtype') is @('*xmm-access*');
     for @('*vex-xmm-access*'), these bits are zeroed out.  For
     @('*ymm-access*'), upper @(`(- 512 256)`) bits are zeroed
     out. For @('*zmm-access*'), no upper bits are zeroed out.</p>"
    :enabled t
    :guard (and (member nbytes '(4 8 16 32 64))
                (unsigned-byte-p (ash nbytes 3) val))
    :returns (x86 x86p :hyp (x86p x86))
    :inline t
    :no-function t
    (case nbytes
      (4  (wz32  index val x86 :regtype regtype))
      (8  (wz64  index val x86 :regtype regtype))
      (16 (wz128 index val x86 :regtype regtype))
      (32 (wz256 index val x86 :regtype regtype))
      (64 (wz512 index val x86))
      (otherwise
       x86))))

(defsection XMMs-Reads-and-Writes

  :parents (ZMMs-Reads-and-Writes register-readers-and-writers)

  :short "Functions to read/write 32/64/128 bits into the XMM
  registers (to be used by non-VEX encoded 128-bit SIMD instructions)"

  :long " <p>These functions are meant to be used by instructions that
  do not use a VEX or EVEX prefix --- these functions preserve the
  upper bits of ZMM registers.  For instructions that use these
  prefixes and zero out these bits instead, see @(see
  ZMMs-Reads-and-Writes).</p>

  <p>Note that the index for accessing the XMM registers is 4-bits
  wide (as opposed to the 5-bit index for ZMM registers --- see @(see
  ZMMs-Reads-and-Writes)) because only 16 XMM registers were supported
  initially in the 64-bit mode (and 8 in the 32-bit mode).</p>

 <p>Source: Intel Vol. 2, Section 2.3.10 --- AVX Instructions
  and Upper 128-bits of YMM registers:</p>

  <blockquote>If an instruction with a destination XMM register is
  encoded with a VEX prefix, the processor zeroes the upper
  bits (above bit 128) of the equivalent YMM register. Legacy SSE
  instructions without VEX preserve the upper bits.</blockquote>

 <p>Functions @(see rx32), @(see rx64), and @(see rx128) will read the
 contents of the XMMs (i.e., low 128 bits of ZMMs) as natural
 numbers.</p>

 <p>Similarly, functions @(see wx32), @(see wx64), and @(see wx128)
 are used to write natural numbers into the XMMs (and preserve the
 upper bits of ZMMs).</p>"

  (local (xdoc::set-default-parents XMMs-Reads-and-Writes))

  (define rx32
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :enabled t
    (rz32 reg x86))

  (define rx64
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :enabled t
    (rz64 reg x86))

  (define rx128
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t
    :no-function t
    :enabled t
    (rz128 reg x86))

  (define wx32
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 32))
     (x86))
    :short "Write @('val') to low 32 bits of a ZMM register; upper
    bits are preserved."
    :inline t
    :no-function t
    :enabled t
    (wz32 reg val x86 :regtype #.*xmm-access*))

  (define wx64
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 64))
     (x86))
    :short "Write @('val') to low 64 bits of a ZMM register; upper
    bits are preserved."
    :inline t
    :no-function t
    :enabled t
    (wz64 reg val x86 :regtype #.*xmm-access*))

  (define wx128
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 128))
     (x86))
    :short "Write @('val') to low 128 bits of a ZMM register; upper
    bits are preserved."
    :inline t
    :no-function t
    :enabled t
    (wz128 reg val x86 :regtype #.*xmm-access*))

  (define xmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 4))
     x86)
    :enabled t
    :guard (member nbytes '(4 8 16))
    :inline t
    :no-function t
    :returns (val natp :rule-classes :type-prescription)
    (case nbytes
      (4  (rx32  index x86))
      (8  (rx64  index x86))
      (16 (rx128 index x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 4, 8, or 16.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       0)))

  (define !xmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 4))
     (val    :type integer)
     x86)
    :short "Write @('val') to low @('nbytes') of an XMM register;
    upper bits of the ZMM register are preserved."
    :enabled t
    :guard (and (member nbytes '(4 8 16))
                (unsigned-byte-p (ash nbytes 3) val))
    :returns (x86 x86p :hyp (x86p x86))
    :inline t
    :no-function t
    (case nbytes
      (4  (wx32  index val x86))
      (8  (wx64  index val x86))
      (16 (wx128 index val x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 4, 8, or 16.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       x86))))

;; ======================================================================

(defsection characterizing-undefined-behavior

  :parents (machine)

  :short "An @('undef') field in the @('x86') state feeds unknown
  values to processor components that are undefined"

  :long "<p>The @('undef') field is used to feed unknown values to
processor components that are undefined, as per the Intel
specifications.  For example, the @('SF'), @('ZF'), @('AF'), and
@('PF') rflags are undefined after a @('MUL') instruction is
executed.</p>

<p>The principle behind the @('undef') field is quite like that of the
@('oracle') sub-field of the @('env') field \(see @(see
environment-field)\).  We describe our use of the @('undef') field by
comparing it to the @('oracle') sub-field.</p>

<p>For reasoning about programs that involve commonly occurring
\"undefined events\" \(like flag computations\), using the @('oracle')
sub-field can be quite tedious, since it has to be carefully
initialized; i.e., a list of appropriate \(symbolic or concrete\)
values has to be associated with the instruction pointer where any
such undefined event occurs.  Imagine doing that for @('SF'), @('ZF'),
@('AF'), and @('PF') every time a @('MUL') instruction is executed.
The reason why we need this initialization is because the only way to
access the @('oracle') is through the functions @(see pop-x86-oracle)
and @(see env-read); @('pop-x86-oracle') expects the @('oracle') to
contain information in a specific format, and @('env-read') will give
us nothing unless we put something in to begin with.</p>

<p>On the other hand, the @('undef') field doesn't require any such
initialization.  The @('undef') field contains a natural number that
is increased every time an undefined value is pulled for use \(using
the constrained function @('create-undef')\) from a pool of undefined
values; thus, every access of the @('undef') field causes it to
contain a new value which is used to seed a unique undefined
value. See @(see undef-read) for details.</p>

<p>There is a reason why we enforced that tediousness in the case of
the @('oracle') sub-field: it provides a way of tracking any
computation that relies on the @('env') field. Such computations don't
happen often, and when they do, it'd probably be better if we knew
exactly what we are expecting from the environment.  Initializing the
@('oracle') is a way of expressing these expectations. However, in the
case of undefined values, we aren't really expecting anything from the
environment.  All we want is a sort of infinite pool of arbitary
values, seeded from @('undef') in our case, that we don't know
anything about.  As such, we wouldn't be able to prove that a value
obtained from @('undef') is equal \(or not\) to any other value,
either obtained from @('undef') or not.  This is exactly what we need
when reasoning about undefined values --- an undefined value is
different from another undefined value, and also all the known
values.</p>"

  )

(encapsulate
  ( ((create-undef *) => *) )

  (local
   (defun create-undef (x)
     (nfix x)))

  (defthm integerp-create-undef
    (integerp (create-undef x))
    :rule-classes (:rewrite :type-prescription))

  (defthm natp-create-undef
    (natp (create-undef x))
    :rule-classes (:rewrite :type-prescription)))

(define unsafe-!undef (v x86)

  :long " <p>Note that @('unsafe-!undef') is enabled, not untouchable,
  and non-executable.  It can be used in proof attempts but not during
  execution.</p>

 <p>@('unsafe-!undef') should be used judiciously because updating the
  @('undef') field with a value it held previously might contaminate
  our 'pool of undefined values', i.e., @(see undef-read) might then
  produce a call of @('create-undef') that collides with a previous
  call of @('create-undef'), which would make the result of an
  equality test between them equal instead of indeterminate.</p>

  <p>An example of an acceptable use of @('unsafe-!undef') is to
  specify the @('undef') field in a final x86 state during a proof
  attempt.</p>"

  :non-executable t
  :enabled t
  :returns (x86 x86p :hyp (x86p x86))
  :parents (undef-read)
  (!undef v x86))

(define undef-read-logic (x86)
  :enabled t
  :returns (mv (unknown natp :rule-classes :type-prescription)
               (x86     x86p :hyp (x86p x86)))
  :parents (undef-read)

  (b* ((undef-seed (nfix (undef x86)))
       (new-unknown (create-undef undef-seed))
       (x86 (!undef (1+ undef-seed) x86)))
    (mv new-unknown x86)))

(define undef-read (x86)
  ;; TO-DO@Shilpi: I'll need to add more args to this function if I
  ;; need the corresponding raw Lisp function to have more info.
  :inline nil
  :enabled t
  :returns (mv (unknown natp :rule-classes :type-prescription)
               (x86     x86p :hyp (x86p x86)))
  :parents (characterizing-undefined-behavior)

  :short "Get a unique unknown to be used when reasoning about
    undefined values in the processor"
  :long "<p>See @(see characterizing-undefined-behavior) for more
  details.</p>

  <p>The accessor and updater functions of the @('undef') field are
  untouchable so that the only way to create a new seed for unknowns
  is via this function.</p>"

  (undef-read-logic x86))

;; We make the following two functions untouchable so that they cannot
;; be used on their own outside function undef-read-logic.

(push-untouchable
 (!undef$inline)
 t)

;; ======================================================================

(defsection rflags-Reads-and-Writes
  :parents (rflag-specifications register-readers-and-writers)
  :short "Reading from and writing to the @('rflags') register in the @('x86') state"

  :long "<p>We define convenient macros @('flgi') and @('!flgi') to read a
   flag's value and to write a flag's value into the @('rflags') field in the
   @('x86') state, respectively.  Additionally, @('!flgi-undefined') can be
   used to write an undefined value into a particular flag.</p>"

  (local (xdoc::set-default-parents rflags-Reads-and-Writes))

  ;; Tips for doing flg RoW proofs:
  ;; (thm (equal (RFLAGSBITS->CF (!rflagsbits->df df rflags))
  ;;             (RFLAGSBITS->CF rflags))
  ;;      ;; Need to enable the following rule for the flag being updated so that
  ;;      ;; the same kind of rule for the other one (RFLAGSBITS->CF-OF-RFLAGSBITS
  ;;      ;; here) can fire.
  ;;      :hints (("Goal" :in-theory (e/d (!RFLAGSBITS->DF-IS-RFLAGSBITS)
  ;;                                      ()))))

  ;; The following works out of the box.
  ;; (thm (equal (RFLAGSBITS->CF (!rflagsbits->cf cf rflags))
  ;;             (bfix cf)))

  (defmacro flgi (flg x86)
    (declare (xargs :guard (keywordp flg)))
    `(b* ((rflags (the (unsigned-byte 32) (rflags ,x86))))
       (case ,flg
         (:cf (rflagsBits->cf rflags))
         (:pf (rflagsBits->pf rflags))
         (:af (rflagsBits->af rflags))
         (:zf (rflagsBits->zf rflags))
         (:sf (rflagsBits->sf rflags))
         (:tf (rflagsBits->tf rflags))
         (:if (rflagsBits->intf rflags))
         (:df (rflagsBits->df rflags))
         (:of (rflagsBits->of rflags))
         (:iopl (rflagsBits->iopl rflags))
         (:nt (rflagsBits->nt rflags))
         (:rf (rflagsBits->rf rflags))
         (:vm (rflagsBits->vm rflags))
         (:ac (rflagsBits->ac rflags))
         (:vif (rflagsBits->vif rflags))
         (:vip (rflagsBits->vip rflags))
         (:id (rflagsBits->id rflags))
         (otherwise
          (er hard 'flgi "~%FLGI: illegal flg keyword: ~x0.~%" ,flg)))))

  (defmacro !flgi (flg val x86)
    (declare (xargs :guard (keywordp flg)))
    `(b* ((rflags (the (unsigned-byte 32) (rflags ,x86)))
          (new-rflags
           (the (unsigned-byte 32)
             (case ,flg
               (:cf   (!rflagsBits->cf ,val rflags))
               (:pf   (!rflagsBits->pf ,val rflags))
               (:af   (!rflagsBits->af ,val rflags))
               (:zf   (!rflagsBits->zf ,val rflags))
               (:sf   (!rflagsBits->sf ,val rflags))
               (:tf   (!rflagsBits->tf ,val rflags))
               (:if   (!rflagsBits->intf ,val rflags))
               (:df   (!rflagsBits->df ,val rflags))
               (:of   (!rflagsBits->of ,val rflags))
               (:iopl (!rflagsBits->iopl ,val rflags))
               (:nt   (!rflagsBits->nt ,val rflags))
               (:rf   (!rflagsBits->rf ,val rflags))
               (:vm   (!rflagsBits->vm ,val rflags))
               (:ac   (!rflagsBits->ac ,val rflags))
               (:vif  (!rflagsBits->vif ,val rflags))
               (:vip  (!rflagsBits->vip ,val rflags))
               (:id   (!rflagsBits->id ,val rflags))
               (otherwise
                (er hard '!flgi "~%!FLGI: illegal flg keyword: ~x0.~%" ,flg))))))
       (!rflags new-rflags ,x86)))

  (define undef-flg-logic (x86)
    :enabled t
    :prepwork ((local (in-theory (e/d* () (undef-read)))))
    :returns (mv (unknown natp :rule-classes :type-prescription)
                 (x86     x86p :hyp (x86p x86)))
    (undef-read x86))

  (define undef-flg (x86)
    ;; I have smashed this function under the hood.  This is a tad more
    ;; efficient than smashing just undef-read when flags are assigned
    ;; undefined values because it helps us avoid calling n01 while
    ;; execution.  This saves one call to the builtin LOGAND that might
    ;; create bignums, potentially.
    :inline nil
    :enabled t
    :prepwork ((local (in-theory (e/d* () (undef-flg-logic)))))
    :returns (mv (unknown-bit bitp :rule-classes :type-prescription)
                 (x86         x86p :hyp (x86p x86)))
    (b* (((mv val x86)
          (undef-flg-logic x86)))
      (mv (n01 val) x86)))

  (defmacro !flgi-undefined (flg x86)
    (declare (xargs :guard (keywordp flg)))
    `(b* ((rflags (the (unsigned-byte 32) (rflags ,x86)))
          ((mv val x86) (undef-flg ,x86))
          (new-rflags
           (the (unsigned-byte 32)
             (case ,flg
               (:cf   (!rflagsBits->cf val rflags))
               (:pf   (!rflagsBits->pf val rflags))
               (:af   (!rflagsBits->af val rflags))
               (:zf   (!rflagsBits->zf val rflags))
               (:sf   (!rflagsBits->sf val rflags))
               (:tf   (!rflagsBits->tf val rflags))
               (:if   (!rflagsBits->intf val rflags))
               (:df   (!rflagsBits->df val rflags))
               (:of   (!rflagsBits->of val rflags))
               (:iopl (!rflagsBits->iopl val rflags))
               (:nt   (!rflagsBits->nt val rflags))
               (:rf   (!rflagsBits->rf val rflags))
               (:vm   (!rflagsBits->vm val rflags))
               (:ac   (!rflagsBits->ac val rflags))
               (:vif  (!rflagsBits->vif val rflags))
               (:vip  (!rflagsBits->vip val rflags))
               (:id   (!rflagsBits->id val rflags))
               (otherwise
                (er hard '!flgi "~%!FLGI-UNDEFINED: illegal flg keyword: ~x0.~%" ,flg))))))
       (!rflags new-rflags ,x86)))

  (define write-user-rflags
    ((user-flags-vector :type (unsigned-byte 32))
     (undefined-mask    :type (unsigned-byte 32))
     x86)

    :inline t
    :no-function t

    :short "Writing user rflags \(CF, PF, AF, ZF, SF, and OF\),
  including undefined ones, to the x86 state"

    :long "<p>We set the undefined flags, which are indicated by
  @('mask'), to the value returned by @(see undef-read).</p>"

    :guard-hints (("Goal" :in-theory (e/d (rflagsBits->cf
                                           rflagsBits->pf
                                           rflagsBits->af
                                           rflagsBits->zf
                                           rflagsBits->sf
                                           rflagsBits->of
                                           rflagsbits-fix)
                                          (unsigned-byte-p
                                           not
                                           (tau-system)))))
    :prepwork ((local (in-theory (e/d ()
                                      (bitops::logand-with-negated-bitmask
                                       fty::unsigned-byte-p-1-when-bitp)))))

    :returns (x86 x86p :hyp (x86p x86))

    (b* ((user-flags-vector
          (mbe :logic (n32 user-flags-vector) :exec user-flags-vector))
         (undefined-mask
          (mbe :logic (n32 undefined-mask) :exec undefined-mask))
         ((the (unsigned-byte 32) input-rflags)
          (mbe :logic (n32 (rflags x86)) :exec (rflags x86))))
    
      (mbe 
       :logic     
       (b* ((x86 (if (equal (rflagsBits->cf undefined-mask) 1)
                     (!flgi-undefined :cf x86)
                   (!flgi :cf (rflagsBits->cf user-flags-vector) x86)))
            (x86 (if (equal (rflagsBits->pf undefined-mask) 1)
                     (!flgi-undefined :pf x86)
                   (!flgi :pf (rflagsBits->pf user-flags-vector) x86)))
            (x86 (if (equal (rflagsBits->af undefined-mask) 1)
                     (!flgi-undefined :af x86)
                   (!flgi :af (rflagsBits->af user-flags-vector) x86)))
            (x86 (if (equal (rflagsBits->zf undefined-mask) 1)
                     (!flgi-undefined :zf x86)
                   (!flgi :zf (rflagsBits->zf user-flags-vector) x86)))
            (x86 (if (equal (rflagsBits->sf undefined-mask) 1)
                     (!flgi-undefined :sf x86)
                   (!flgi :sf (rflagsBits->sf user-flags-vector) x86)))
            (x86 (if (equal (rflagsBits->of undefined-mask) 1)
                     (!flgi-undefined :of x86)
                   (!flgi :of (rflagsBits->of user-flags-vector) x86))))
         x86)
       :exec
       (if (eql undefined-mask 0)
           (b* ((x86 (!flgi :cf (rflagsBits->cf user-flags-vector) x86))
                (x86 (!flgi :pf (rflagsBits->pf user-flags-vector) x86))
                (x86 (!flgi :af (rflagsBits->af user-flags-vector) x86))
                (x86 (!flgi :zf (rflagsBits->zf user-flags-vector) x86))
                (x86 (!flgi :sf (rflagsBits->sf user-flags-vector) x86))
                (x86 (!flgi :of (rflagsBits->of user-flags-vector) x86)))
             x86)
         (b* ((x86 (if (equal (rflagsBits->cf undefined-mask) 1)
                       (!flgi-undefined :cf x86)
                     (!flgi :cf (rflagsBits->cf user-flags-vector) x86)))
              (x86 (if (equal (rflagsBits->pf undefined-mask) 1)
                       (!flgi-undefined :pf x86)
                     (!flgi :pf (rflagsBits->pf user-flags-vector) x86)))
              (x86 (if (equal (rflagsBits->af undefined-mask) 1)
                       (!flgi-undefined :af x86)
                     (!flgi :af (rflagsBits->af user-flags-vector) x86)))
              (x86 (if (equal (rflagsBits->zf undefined-mask) 1)
                       (!flgi-undefined :zf x86)
                     (!flgi :zf (rflagsBits->zf user-flags-vector) x86)))
              (x86 (if (equal (rflagsBits->sf undefined-mask) 1)
                       (!flgi-undefined :sf x86)
                     (!flgi :sf (rflagsBits->sf user-flags-vector) x86)))
              (x86 (if (equal (rflagsBits->of undefined-mask) 1)
                       (!flgi-undefined :of x86)
                     (!flgi :of (rflagsBits->of user-flags-vector) x86))))
           x86))))

    ///

    (local (in-theory (e/d (undef-read) ())))

    (defthm xr-write-user-rflags
      (implies (and (not (equal fld :rflags))
                    (not (equal fld :undef)))
               (equal (xr fld index (write-user-rflags flags mask x86))
                      (xr fld index x86)))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm xr-write-user-rflags-no-mask
      ;; Do we need this?
      (implies (not (equal fld :rflags))
               (equal (xr fld index (write-user-rflags flags 0 x86))
                      (xr fld index x86)))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm rflags-and-write-user-rflags-no-mask
      (equal (write-user-rflags user-flags-vector 0 x86)
             (b* ((x86 (!flgi :cf (rflagsBits->cf user-flags-vector) x86))
                  (x86 (!flgi :pf (rflagsBits->pf user-flags-vector) x86))
                  (x86 (!flgi :af (rflagsBits->af user-flags-vector) x86))
                  (x86 (!flgi :zf (rflagsBits->zf user-flags-vector) x86))
                  (x86 (!flgi :sf (rflagsBits->sf user-flags-vector) x86))
                  (x86 (!flgi :of (rflagsBits->of user-flags-vector) x86)))
               x86))
      :hints (("Goal" :in-theory (e/d* (rflagsBits->cf
                                        rflagsBits->pf
                                        rflagsBits->af
                                        rflagsBits->zf
                                        rflagsBits->sf
                                        rflagsBits->of
                                        rflagsbits-fix)
                                       (force (force))))))))


;; ======================================================================

(include-book "tools/include-raw" :dir :system)
(defttag :undef-flg)
(include-raw "register-readers-and-writers-raw.lsp"
             :on-compile-fail
             (format t "[register-readers-and-writers-raw.lsp] Compilation failed with message ~a~%"
                     condition)
             :on-load-fail
             (cw "[register-readers-and-writers-raw.lsp] Load failed; Moving On.~%")
             :host-readtable t)

;; ======================================================================
