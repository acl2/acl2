; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; The Intel and AMD documentation is ambiguous about the determination of the
; operand size of the PUSH and POP instructions in 64-bit mode.
;
; The PUSH and POP instruction reference in Intel manual, Mar'17, Vol. 2 says
; that the D flag of the current code segment descriptor determines the default
; operand size, and that this default size may be overridden by instruction
; prefixes 66H or REX.W. Section 3.4.5 of Vol. 3A says (in the description of
; the L bit, just before Section 3.4.5.1 starts) that in 64-bit mode the L bit
; is 1 and that therefore the D bit is 0. The same Section 3.4.5 (in the
; description of the D/B bit, a little before the description of the L bit),
; says that when D is 0 the default operand size is 16 bits. Table 2-4 of
; Vol. 2A says that if the W bit of the REX prefix is 1 then the operand size
; is 64 bits; otherwise it is as determined by CS.D (i.e. 16 bits, as mentioned
; above).  Section 2.2.1.2 of Vol. 2A (where Table 2-4 is) says that the 66H
; prefix is ignored when REX.W is 1, and that if there is a 66H prefix and
; REX.W is 0 then the operand size is 16 bits. From these parts of the
; documentation, we would conclude that in 64-bit mode the operand size for
; PUSH and POP is 64 bits if REX.W is 1, otherwise it is 16 bits, and the 66H
; prefix is irrelevant. (Note that the tables at the beginning of the PUSH and
; POP instructions disallow a 32-bit operand size in 64-bit mode.)
;
; However, the PUSH and POP instruction reference in AMD manual, Jun'15, Vol. 3
; says that in 64-bit mode the default operand size is 64 bits. Furthermore,
; Table A-2 of Intel manual, Vol. 2D shows a d64 superscript for the PUSH and
; POP instructions that are valid and encodable in 64-bit mode (except for the
; PUSH r/m16 and PUSH r/m64 instructions, perhaps because their FFH opcode also
; encodes the INC/DEC instructions). According to Table A-1 in Intel manual
; Vol. 2D, the d64 superscript means that the default operand size is 64 bits
; (and that a 32-bit operand size cannot be encoded). These d64 superscripts
; are consistent with the AMD instruction reference for PUSH and POP. From
; these parts of the documentation, we would conclude that in 64-bit mode the
; operand size for PUSH and POP is 64 bits by default, that it can be
; overridden by a 66H prefix, and that REX.W is irrelevant.
;
; Also based on some experiments, we choose the second intepretations above in
; our formal model.
;
; The documentation of PUSH in Intel manual, Mar'17, Vol. 2 includes a section
; "IA-32 Architecture Compatibiity" describing a slightly different behavior of
; PUSH ESP in 8086 processors. This is is currently not covered by our formal
; model below. To cover this, we may need to extend the X86 state with
; information about the kind of processor.

;; ======================================================================
;; INSTRUCTION: (one- and two- byte opcode maps)
;; push
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-push-general-register
  :parents (one-byte-opcodes)

  :short "PUSH: 50+rw/rd"

  :long "<p>Op/En: O</p>
   <p><tt>50+rw/rd r16/r32/r64</tt></p>
   <p>Note that <tt>50+rd r32</tt> is N.E. in 64-bit mode
      and that <tt>50+rd r64</tt> is N.E. in 32-bit mode.</p>

   <p>PUSH does not have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled with the execution in
   this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body

  (b* ((ctx 'x86-push-general-register)

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ;; See "Z" in http://ref.x86asm.net/geek.html#x50
       (reg (mbe :logic (loghead 3 opcode)
                 :exec (the (unsigned-byte 3)
                            (logand #x07 opcode))))
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (val (rgfi-size operand-size (reg-index reg rex-byte #.*b*) rex-byte
                       x86))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       ((mv flg x86)
        (wme-size
         operand-size
         (the (signed-byte #.*max-linear-address-size*) new-rsp)
         *ss*
         val
         (alignment-checking-enabled-p x86)
         x86
         :mem-ptr? nil))
       ((when flg) ;; Would also handle bad rsp values.
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that in add-to-*sp above.
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))

       (x86 (write-*sp new-rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x50 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x51 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x52 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x53 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x54 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x55 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x56 '(:nil nil)
                                      'x86-push-general-register)
    (add-to-implemented-opcodes-table 'PUSH #x57 '(:nil nil)
                                      'x86-push-general-register)))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-push-Ev
  :parents (one-byte-opcodes)

  :short "PUSH: FF /6 r/m"

  :long "<p>Op/En: M</p>
   <p><tt>FF /6 r/m16/32/64</tt></p>
   <p>Note that <tt>FF/6 r/m32</tt> is N.E. in 64-bit mode
      and that <tt>FF/6 r/m64</tt> is N.E. in 32-bit mode.</p>

   <p>PUSH does not have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled with the execution in
   this case.</p>

   <p>This opcode belongs to Group 5, and it has an opcode
   extension (ModR/m.reg = 6).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn (add-to-implemented-opcodes-table 'PUSH #xFF '(:reg 6) 'x86-push-Ev))

  :body

  (b* ((ctx 'x86-push-Ev)

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))
       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))

       ((mv flg new-rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by) ?E-addr x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                operand-size
                                                t ; do alignment checking
                                                nil ;; Not a memory pointer operand
                                                seg-reg
                                                p4?
                                                temp-rip
                                                rex-byte
                                                r/m
                                                mod
                                                sib
                                                0 ;; No immediate operand
                                                x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg temp-rip) (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!fault-fresh :gp 0 :increment-ip-error flg)) ;; #GP(0)

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:

       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  E
                  (alignment-checking-enabled-p x86)
                  x86
                  :mem-ptr? nil))
       ((when flg) ;; Would also handle bad rsp values.
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that in add-to-*sp above.
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned new-rsp)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))

       (x86 (write-*sp new-rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-push-I

  :parents (one-byte-opcodes)

  :short "PUSH: 6A/68 ib/iw/id"

  :long "<p>Op/En: I</p>
   <p><tt>6A ib</tt>: PUSH imm8</p>
   <p><tt>68 iw</tt>: PUSH imm16</p>
   <p><tt>68 id</tt>: PUSH imm32</p>

   <p>From the description of the PUSH instruction \(Intel Manual, Vol. 2,
   Section 4.2\):</p>

   <p><i> If the source operand is an immediate of size less than the operand
   size, a sign-extended value is pushed on the stack.</i></p>

   <p>PUSH doesn't have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled the decoding with the
   execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :guard-hints (("Goal" :in-theory (enable rime-size)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x68 '(:nil nil)
                                      'x86-push-I)
    (add-to-implemented-opcodes-table 'PUSH #x6A '(:nil nil)
                                      'x86-push-I))

  :body

  (b* ((ctx 'x86-push-I)

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       (byte-imm? (eql opcode #x6A))
       ((the (integer 1 8) imm-size)
        (select-operand-size byte-imm? rex-byte t prefixes x86))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg0 (the (signed-byte 32) imm) x86)
        (rime-size imm-size temp-rip *cs* :x nil x86))
       ((when flg0)
        (!!ms-fresh :imm-rime-size-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip imm-size x86))
       ((when flg)
        (!!fault-fresh :gp 0 :temp-rip-not-canonical temp-rip)) ;; #GP(0)

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       ((mv flg1 x86)
        (wme-size operand-size
                  new-rsp
                  *ss*
                  (mbe :logic (loghead (ash operand-size 3) imm)
                       :exec (logand
                              (case operand-size
                                (2 #.*2^16-1*)
                                (4 #.*2^32-1*)
                                (8 #.*2^64-1*))
                              (the (signed-byte 32) imm)))
                  (alignment-checking-enabled-p x86)
                  x86
                  :mem-ptr? nil))
       ((when flg1) ;; Would also handle "bad" rsp values.
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that in add-to-*sp above.
         ((and (consp flg1) (eql (car flg1) :non-canonical-address))
          (!!fault-fresh :ss 0 :new-rsp-not-canonical flg1)) ;; #SS(0)
         ((and (consp flg1) (eql (car flg1) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :new-rsp-unaligned flg1)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg1))))

       (x86 (write-*sp new-rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-push-segment-register
  :parents (one-byte-opcodes two-byte-opcodes)

  :short "PUSH FS/GS"
  :long
  "<p><tt>0E</tt>:    \[PUSH CS\]</p>
   <p><tt>16</tt>:    \[PUSH SS\]</p>
   <p><tt>1E</tt>:    \[PUSH DS\]</p>
   <p><tt>06</tt>:    \[PUSH ES\]</p>
   <p><tt>0F A0</tt>: \[PUSH FS\]</p>
   <p><tt>0F A8</tt>: \[PUSH GS\]</p>

   <p>If the source operand is a segment register \(16 bits\) and the operand
   size is 64-bits, a zero- extended value is pushed on the stack; if the
   operand size is 32-bits, either a zero-extended value is pushed on the stack
   or the segment selector is written on the stack using a 16-bit move. For the
   last case, all recent Core and Atom processors perform a 16-bit move,
   leaving the upper portion of the stack location unmodified.</p>

   <p>PUSH doesn't have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled with the execution in
   this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x0E '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x16 '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x1E '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x06 '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x0FA0 '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x0FA8 '(:nil nil)
                                      'x86-push-segment-register))

  :body

  (b* ((ctx 'x86-push-general-register)

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ;; PUSH CS/SS/DS/ES are invalid in 64-bit mode:
       ((when (and (64-bit-modep x86)
                   (member opcode '(#x0E #x16 #x1E #x06))))
        (!!fault-fresh :ud nil :push-segment-64-bit-mode opcode)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((the (unsigned-byte 16) val)
        (seg-visiblei (case opcode
                        (#x0E *CS*)
                        (#x16 *SS*)
                        (#x1E *DS*)
                        (#x06 *ES*)
                        (#xA0 *FS*)
                        (t *GS*))
                      x86))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:

       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  ;; If operand-size is 64, val is zero-extended here
                  ;; automatically.
                  val
                  (alignment-checking-enabled-p x86)
                  x86
                  :mem-ptr? nil))
       ((when flg) ;; Would also handle bad rsp values.
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that above.
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))

       (x86 (write-*sp new-rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

;; ======================================================================
;; INSTRUCTION: (one-byte opcode map)
;; pop
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-pop-general-register
  :parents (one-byte-opcodes)

  :short "POP: 58+rw/rd"
  :long "<p>Op/En: O</p>
   <p><tt>58+rw/rd r16/r32/r64</tt></p>
   <p>Note that <tt>58+rd r32</tt> is N.E. in the 64-bit mode
      and that <tt>58+rd r64</tt> is N.E. in 32-bit mode.</p>

   <p>POP does not have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled with the execution in
   this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :body

  (b* ((ctx 'x86-pop-general-register)

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))

       ((mv flg new-rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r (alignment-checking-enabled-p x86) x86
                  :mem-ptr? nil))
       ((when flg0)
        (cond
         ;; FIXME? The non-canonical-address error won't come
         ;; up here because we already check for that in add-to-*sp
         ;; above.
         ((and (consp flg0) (eql (car flg0) :non-canonical-address))
          (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; #SS(0)
         ((and (consp flg0) (eql (car flg0) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg0))))

       ;; See "Z" in http://ref.x86asm.net/geek.html#x58.
       (reg (logand opcode #x07))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:
       ;; (Intel manual, Mar'17, Vol. 2 says, in the specification of POP,
       ;; that a POP SP/ESP/RSP instruction increments the stack pointer
       ;; before the popped data is written into the stack pointer,
       ;; so the order of the following two bindings is important)
       (x86 (write-*sp new-rsp x86))
       (x86
        ;; See Intel Table 3.1, p.3-3, Vol. 2-A
        (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
                    val rex-byte x86))
       (x86 (write-*ip temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (enable rme-size)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'POP #x58 '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x59 '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5A '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5B '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5C '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5D '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5E '(:nil nil) 'x86-pop-general-register)
    (add-to-implemented-opcodes-table 'POP #x5F '(:nil nil) 'x86-pop-general-register)))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-pop-Ev
  :parents (one-byte-opcodes)

  :short "POP: 8F/0 r/m"

  :long "<p>Op/En: M</p>
   <p><tt>8F/0 r/m16/32/64</tt></p>
   <p>Note that <tt>8F/0 r/m32</tt> is N.E. in 64-bit mode
      and that <tt>8F/0 r/m64</tt> is N.E. in 32-bit mode.</p>

   <p>POP does not have a separate instruction semantic function, unlike other
   opcodes like ADD, SUB, etc. The decoding is coupled with the execution in
   this case.</p>

   <p>This opcode belongs to Group 1A, and it has an opcode
   extension (ModR/m.reg = 0).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'POP #x8F '(:reg 0) 'x86-pop-Ev)

  :body

  (b* ((ctx 'x86-pop-Ev)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))

       ((mv flg new-rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       (check-alignment? (alignment-checking-enabled-p x86))
       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r check-alignment? x86
                  :mem-ptr? nil))
       ((when flg0)
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that in add-to-*sp above.
         ((and (consp flg0) (eql (car flg0) :non-canonical-address))
          (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; #SS(0)
         ((and (consp flg0) (eql (car flg0) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg0)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg0))))

       ((mv flg1
            (the (signed-byte 64) addr)
            (the (unsigned-byte 3) increment-RIP-by)
            x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg1) ;; #SS exception?
        (!!ms-fresh :x86-effective-addr-error flg1))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       ((mv flg temp-rip) (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!fault-fresh :gp 0 :increment-ip-error flg)) ;; #GP(0)

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Update the x86 state:

       ;; Intel manual, Mar'17, Vol. 2 says, in the specification of POP,
       ;; that a POP SP/ESP/RSP instruction increments the stack pointer
       ;; before the popped data is written into the stack pointer.
       ;; Thus, we must write to the stack pointer before the operand.

       (x86 (write-*sp new-rsp x86))

       ((mv flg3 x86)
        (x86-operand-to-reg/mem$ operand-size
                                 check-alignment?
                                 nil ;; Not a memory pointer operand
                                 val
                                 seg-reg
                                 addr
                                 rex-byte
                                 r/m
                                 mod
                                 x86))
       ((when flg3)
        (!!ms-fresh :x86-operand-to-reg/mem flg3))

       (x86 (write-*ip temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (enable rme-size)))
  )

;; (def-inst x86-pop-segment-register
;;   :parents (one-byte-opcodes)

;;   :short "POP FS/GS"
;;   :long "<p><tt>0F A1</tt>: \[POP FS\]</p>
;; <p><tt>0F A9</tt>: \[POP GS\]</p>
;;    <p>Popping other segment registers in the 64-bit mode is
;;    invalid.</p>

;; <p>If the source operand is a segment register \(16 bits\) and the
;;  operand size is 64-bits, a zero- extended value is pushed on the
;;  stack; if the operand size is 32-bits, either a zero-extended value
;;  is pushed on the stack or the segment selector is written on the
;;  stack using a 16-bit move. For the last case, all recent Core and
;;  Atom processors perform a 16-bit move, leaving the upper portion of
;;  the stack location unmodified.</p>

;; <p>POP doesn't have a separate instruction semantic function, unlike
;; other opcodes like ADD, SUB, etc. I've just coupled the decoding with
;; the execution in this case.</p>"

;;   :returns (x86 x86p :hyp (and (x86p x86)
;;                                (canonical-address-p temp-rip)))

;;   :guard-debug t

;;   :body

;;   (b* ((ctx 'x86-pop-Ev)
;;        (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
;;        ((when lock)
;;         (!!ms-fresh :lock-prefix prefixes))
;;        (p2 (prefixes-slice :group-2-prefix prefixes))
;;        (p3 (equal #.*operand-size-override*
;;               (prefixes-slice :group-3-prefix prefixes)))

;;        (r/m (mrm-r/m modr/m))
;;        (mod (mrm-mod modr/m))

;;        ((the (integer 1 8) operand-size)
;;         (if p3
;;             2
;;           ;; 4-byte operand size is N.E. in 64-bit mode
;;           8))

;;        (rsp (rgfi *rsp* x86))
;;        ((when (not (canonical-address-p rsp)))
;;         (!!ms-fresh :rsp-not-canonical rsp))

;;        ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
;;         (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
;;        ;; TO-DO@Shilpi: Raise a #SS exception.
;;        ((when (not (canonical-address-p new-rsp)))
;;         (!!ms-fresh :new-rsp-not-canonical new-rsp))

;;        ((mv flg0 val x86)
;;         (rme-size operand-size rsp *ss* :r x86))
;;        ((when flg0) ;; #SS exception?
;;         (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; #SS(0)

;;        (p4 (equal #.*addr-size-override*
;;               (prefixes-slice :group-4-prefix prefixes)))
;;        ((mv flg1 v-addr (the (unsigned-byte 3) increment-RIP-by) x86)
;;         (if (equal mod #b11)
;;             (mv nil 0 0 x86)
;;           (x86-effective-addr p4 temp-rip rex-byte r/m mod sib 0 x86)))
;;        ((when flg1) ;; #SS exception?
;;         (!!ms-fresh :x86-effective-addr-error flg1))

;;        ((mv flg2 v-addr)
;;         (case p2
;;           (0 (mv nil v-addr))
;;           ;; TO-DO@Shilpi: I don't really need to check whether FS and
;;           ;; GS base are canonical or not.  On the real machine, if
;;           ;; the MSRs containing these bases are assigned
;;           ;; non-canonical addresses, an exception is raised.
;;           (#.*fs-override*
;;            (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
;;                   (fs-base (n64-to-i64 nat-fs-base)))
;;              (if (not (canonical-address-p fs-base))
;;                  (mv 'Non-Canonical-FS-Base fs-base)
;;                (mv nil (+ fs-base v-addr)))))
;;           (#.*gs-override*
;;            (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
;;                   (gs-base (n64-to-i64 nat-gs-base)))
;;              (if (not (canonical-address-p gs-base))
;;                  (mv 'Non-Canonical-GS-Base gs-base)
;;                (mv nil (+ gs-base v-addr)))))
;;           (t (mv 'Unidentified-P2 v-addr))))
;;        ((when flg2)
;;         (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg2))
;;        ((when (not (canonical-address-p v-addr)))
;;         (!!ms-fresh :v-addr-not-canonical v-addr))

;;        ((mv flg3 x86)
;;         (x86-operand-to-reg/mem
;;          operand-size val v-addr rex-byte r/m mod x86))
;;        ((when flg3)
;;         (!!ms-fresh :x86-operand-to-reg/mem flg2))

;;        ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
;;         (+ increment-RIP-by temp-rip))
;;        ((when (not (canonical-address-p temp-rip)))
;;         (!!ms-fresh :virtual-memory-error temp-rip))

;;        ;; TO-DO@Shilpi: If the instruction goes beyond 15 bytes, stop. Change
;;        ;; to an exception later.
;;        ((when (> (- temp-rip start-rip) 15))
;;         (!!ms-fresh :instruction-length (- temp-rip start-rip)))

;;        ;; Update the x86 state:
;;        (x86 (!rgfi *rsp* new-rsp x86))
;;        (x86 (!rip temp-rip x86)))

;;       x86))

;; ======================================================================
;; INSTRUCTION: PUSHF/PUSHFQ
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-pushf

  ;; #x9C: Op/En: NP
  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'PUSHF #x9C '(:nil nil) 'x86-pushf)

  :body

  (b* ((ctx 'x86-pushf)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))
       ((mv flg new-rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((the (unsigned-byte 32) eflags) (rflags x86))

       ((the (unsigned-byte 32) eflags)
        (case operand-size
          ;; Lower 16 bits are stored on the stack
          (2 (logand #xffff eflags))
          ;; VM and RF rflag bits are cleared in the image stored on the
          ;; stack.  Also, bits from 22-63 are reserved, and hence,
          ;; zeroed out.
          (otherwise (logand #x3cffff eflags))))

       ;; We don't need to check for valid length for one-byte
       ;; instructions.  The length will be more than 15 only if
       ;; get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.

       ;; Update the x86 state:
       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  eflags
                  (alignment-checking-enabled-p x86)
                  x86
                  :mem-ptr? nil))
       ((when flg)
        (cond
         ;; FIXME? The non-canonical-address error won't come
         ;; up here because we already check for that in above.
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :wme-size-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))
       (x86 (write-*sp new-rsp x86))
       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: POPF/POPFQ
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-popf

  ;; #x9D
  ;; Op/En: NP

  ;; Intel Vol. 2B, p. 4-350 says: "In 64-bit mode, use REX.w to pop
  ;; the top of stack to RFLAGS.  POPFQ pops 64-bits from the stack,
  ;; loads the lower 32 bits into rflags, and zero-extends the upper
  ;; bits of eflags."
  ;; TODO: the text just above does not refer to the latest manual (May 2018),
  ;; which does not seem to contain that text in the page for POPF/POPFD/POPFQ;
  ;; should this text be removed?

  ;; TO-DO@Shilpi: For the time being, I am going to assume that the
  ;; CPL is 0.

  ;; 64-bit and 32-bit mode operation of x86-popf:
  ;; (we do not model real-address, virtual-8086, and VME -- Intel Table 4-15)

  ;; if cpl > 0 then

  ;;    if operand-size = 8 or operand-size = 4 then

  ;;       if cpl > iopl then
  ;;          rflags := 64-bit-pop()
  ;;          IF, IOPL, RF, VIP, and all reserved bits are unaffected,
  ;;          VIP and VIF are cleared, all other non-reserved-bits can
  ;;          be modified.

  ;;       else

  ;;          rflags := 64-bit-pop()
  ;;          Same as above, but IF can be modified too.

  ;;       end if

  ;;    else (if operand-size = 2)
  ;;       rflags[15:0] := 16-bit-pop()
  ;;       IOPL and all reserved bits are unaffected, other
  ;;       non-reserved bits can be modified.

  ;;    end if

  ;; else (if cpl = 0)

  ;;    if operand-size = 8 then
  ;;       rflags := 64-bit-pop()
  ;;       RF, VM, and all reserved bits are unaffected, VIP and VIF
  ;;       are cleared, all other non-reserved flags can be modified.

  ;;    else (if operand-size = 2)
  ;;      eflags[15:0] := 16-bit-pop()
  ;;      All non-reserved flags can be modified

  ;;    end if

  ;; end if

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'POPF #x9D '(:nil nil) 'x86-popf)

  :body

  (b* ((ctx 'x86-popf)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) operand-size)
        (if (64-bit-modep x86)
            (if p3? 2 8)
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (rsp (read-*sp x86))

       ((mv flg new-rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r (alignment-checking-enabled-p x86) x86
                  :mem-ptr? nil))
       ((when flg0)
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that above.
         ((and (consp flg0) (eql (car flg0) :non-canonical-address))
          (!!fault-fresh :ss 0 :riml64-error flg0)) ;; #SS(0)
         ((and (consp flg0) (eql (car flg0) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned flg0)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg0))))

       ((the (unsigned-byte 32) val)
        ;; All reserved bits should be unaffected.  This ensures that the bit 1
        ;; of rflags is set, and bits 3, 5, 15, and 22-63 are cleared.
        (logior 2 (the (unsigned-byte 32) (logand #x3f7fd7 val))))

       ;; Update the x86 state:
       (x86 (write-*sp new-rsp x86))
       (x86
        (case operand-size
          (2
           ;; All non-reserved flags can be modified
           (!rflags val x86))

          (otherwise
           ;; VIP and VIF cleared.  RF, VM unaffected.  Other non-reserved
           ;; flags can be modified.
           (let* ((rf (the (unsigned-byte 1) (flgi #.*rf* x86)))
                  (vm (the (unsigned-byte 1) (flgi #.*vm* x86)))
                  (x86 (!rflags val x86))
                  (x86 (!flgi #.*rf* rf x86))
                  (x86 (!flgi #.*vm* vm x86))
                  (x86 (!flgi #.*vip* 0 x86))
                  (x86 (!flgi #.*vif* 0 x86)))
             x86))))

       ;; We don't need to check for valid length for one-byte
       ;; instructions.  The length will be more than 15 only if
       ;; get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.

       (x86 (write-*ip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: PUSHA/PUSHAD
;; ======================================================================

;; Added by Alessandro Coglio <coglio@kestrel.edu>

(def-inst x86-pusha

  :parents (one-byte-opcodes)

  :short "PUSHA/PUSHAD: 60"

  :long
  "<p>
   In 64-bit mode, this instruction is invalid; it throws a #UD exception.
   </p>
   <p>
   Note that the stack pointer is read twice:
   via  @(tsee read-*sp) and via @(tsee rgfi-size).
   The former is used as the address to write into the stack,
   while the latter is used as (part of) the data to write into the stack.
   In principle, the sizes of these two stack pointers may differ:
   the former's size is determined solely by CS.D,
   while the latter's size is also influenced
   by the operand size override prefix.
   It seems odd that the two sizes would differ, though.
   </p>
   <p>
   We use some simple and repetitive code to write the registers into the stack.
   It may be possible to optimize it by pushing all the registers in one shot.
   </p>"

  :implemented
  (add-to-implemented-opcodes-table 'pusha #x60 '(:nil nil) 'x86-pusha)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :prepwork
  ((local (in-theory (e/d* () ((tau-system))))))
  :body

  (b* ((ctx 'x86-pusha)

       ((when (64-bit-modep x86)) (!!fault-fresh :ud nil)) ;; #UD

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ((the (integer 2 4) operand-size)
        (select-operand-size nil 0 nil prefixes x86))

       (rsp (read-*sp x86))

       (eax/ax (rgfi-size operand-size *rax* 0 x86))
       (ecx/cx (rgfi-size operand-size *rcx* 0 x86))
       (edx/dx (rgfi-size operand-size *rdx* 0 x86))
       (ebx/bx (rgfi-size operand-size *rbx* 0 x86))
       (esp/sp (rgfi-size operand-size *rsp* 0 x86))
       (ebp/bp (rgfi-size operand-size *rbp* 0 x86))
       (esi/si (rgfi-size operand-size *rsi* 0 x86))
       (edi/di (rgfi-size operand-size *rdi* 0 x86))

       ;; Because it suffices to check the initial stack pointer for
       ;; alignment just once here, we bypass alignment checking from
       ;; the second call of wme-size onwards.
       (check-alignment? (alignment-checking-enabled-p x86))

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* eax/ax check-alignment? x86 :mem-ptr? nil))
       ((when flg)
        (cond
         ;; FIXME? The non-canonical-address error won't come up here
         ;; because we already check for that in add-to-*sp above.
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :push flg)) ;; #AC(0)
         (t                                ;; Unclassified error!
          (!!fault-fresh flg))))

       (check-alignment? nil)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* ecx/cx check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* edx/dx check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* ebx/bx check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* esp/sp check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* ebp/bp check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* esi/si check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       ((mv flg rsp) (add-to-*sp rsp (- operand-size) x86))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)
       ((mv flg x86) (wme-size operand-size rsp *ss* edi/di check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :push flg)) ;; #SS(0)

       (x86 (write-*sp rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

;; ======================================================================
;; INSTRUCTION: POPA/POPAD
;; ======================================================================

;; Added by Alessandro Coglio <coglio@kestrel.edu>

(def-inst x86-popa

  :parents (one-byte-opcodes)

  :short "POPA/POPD: 61"

  :long
  "<p>
   In 64-bit mode, this instruction is invalid; it throws a #UD exception.
   </p>
   <p>
   We use some simple and repetitive code to read the registers from the stack.
   It may be possible to optimize it by popping all the registers in one shot.
   </p>"

  :implemented
  (add-to-implemented-opcodes-table 'popa #x61 '(:nil nil) 'x86-popa)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :prepwork
  ( ;; I wouldn't need the following two lemmas if I left tau enabled.
   ;; Since tau slows the guard proof down, I'd rather have these
   ;; lemmas here locally.
   (local
    (defthm integerp-of-rme16-value
      (implies (x86p x86)
               (b* (((mv ?flg ?word ?x86-new)
                     (rme16 eff-addr
                            seg-reg r-x check-alignment? x86)))
                 (integerp word)))))

   (local
    (defthm integerp-of-rme32-value
      (implies (x86p x86)
               (b* (((mv ?flg ?dword ?x86-new)
                     (rme32 eff-addr seg-reg
                            r-x check-alignment? x86 :mem-ptr? mem-ptr?)))
                 (integerp dword)))))

   (local (in-theory (e/d* (rme-size-of-2-to-rme16
                            rme-size-of-4-to-rme32)
                           ((tau-system))))))

  :body
  (b* ((ctx 'x86-popa)

       ((when (64-bit-modep x86)) (!!fault-fresh :ud nil)) ;; #UD

       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ((the (integer 2 4) operand-size)
        (select-operand-size nil 0 nil prefixes x86))

       (rsp (read-*sp x86))

       ;; Because it suffices to check the initial stack pointer for
       ;; alignment just once here, we bypass alignment checking from
       ;; the second call of rme-size onwards.
       (check-alignment? (alignment-checking-enabled-p x86))

       ((mv flg edi/di x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg)
        (cond
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :pop flg)) ;; #AC(0)
         (t                               ;; Unclassified error!
          (!!fault-fresh flg))))
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       (check-alignment? nil)

       ((mv flg esi/si x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg ebp/bp x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ;; pushed ESP/SP is not actually read (see pseudocode in
       ;; Intel manual, Mar'17, Volume 2, POPA/POPAD reference):
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg ebx/bx x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg edx/dx x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg ecx/cx x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg eax/ax x86) (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)
       ((mv flg rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       (x86 (!rgfi-size operand-size *rdi* edi/di 0 x86))
       (x86 (!rgfi-size operand-size *rsi* esi/si 0 x86))
       (x86 (!rgfi-size operand-size *rbp* ebp/bp 0 x86))
       ;; ESP/SP is not actually written (see pseudocode in
       ;; Intel manual, Mar'17, Volume 2, POPA/POPAD reference)
       (x86 (!rgfi-size operand-size *rbx* ebx/bx 0 x86))
       (x86 (!rgfi-size operand-size *rdx* edx/dx 0 x86))
       (x86 (!rgfi-size operand-size *rcx* ecx/cx 0 x86))
       (x86 (!rgfi-size operand-size *rax* eax/ax 0 x86))

       (x86 (write-*sp rsp x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

;; ======================================================================
