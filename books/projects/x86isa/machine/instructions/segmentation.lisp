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
(local (include-book "../guard-helpers"))

;; No alignment check is done for these instructions because they are
;; supervisor-level instructions.

;; ======================================================================
;; INSTRUCTION: LGDT
;; ======================================================================

(def-inst x86-lgdt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :long

  "<h3>Op/En = M: \[OP m16@('&')m32\]</h3>
   <h3>Op/En = M: \[OP m16@('&')m64\]</h3>

   <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
   bytes (an 8-byte base and a 2-byte limit).</p>

   <p>\[OP  M\]<br/>
   0F 01/2: LGDT m16@('&')32<br/>
   0F 01/2: LGDT m16@('&')64</p>

   <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
   a non-canonical form, raise the SS exception.</p>"

  :guard (not (equal (modr/m->mod modr/m) #b11))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* (((when (app-view x86))
        (!!ms-fresh :lgdt-unimplemented-in-app-view))

       ;; If the current privilege level is not 0, the #GP exception is raised
       ;; --- this is handled during dispatch; see opcode-maps for details.

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((the (integer 4 8) base-size)
        (if (64-bit-modep x86) 8 4))

       ((the (integer 6 10) base-size+2) (+ 2 base-size))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0
            mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode 0
                                                base-size+2
                                                inst-ac?
                                                t ;; Memory pointer operand
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; The operand size attribute is needed because, according to Intel
       ;; manual, May'18, specification of LGDT, only 24 bits from the base are
       ;; copied into GDTR when the operand size attribute is 16 bits.
       (p3? (eql #.*operand-size-override*
                 (prefixes->opr prefixes)))
       (operand-size
        (if (eql base-size 8)
            8
          (b* (((the (unsigned-byte 16) cs-attr)
                (xr :seg-hidden-attr #.*cs* x86))
               (cs.d
                (code-segment-descriptor-attributesBits->d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))
       (base-bits (case operand-size
                    (8 64)
                    (4 32)
                    (t 24)))

       ;; Load the memory operand in the GDTR register.
       (gdtr-limit
        (!gdtr/idtrBits->limit
                                 (part-select mem :low 0 :width 16)
                                 0))
       (gdtr
        (!gdtr/idtrBits->base-addr
                                 (part-select mem :low 16 :width base-bits)
                                 gdtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *gdtr* gdtr x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LIDT
;; ======================================================================

(def-inst x86-lidt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard (not (equal (modr/m->mod modr/m) #b11))

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :long

  "<h3>Op/En = M: \[OP m16@('&')m32\]</h3>
   <h3>Op/En = M: \[OP m16@('&')m64\]</h3>

   <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
   bytes (an 8-byte base and a 2-byte limit).</p>

   <p>\[OP  M\]<br/>
   0F 01/3: LIDT m16@('&')32<br/>
   0F 01/3: LIDT m16@('&')64</p>

   <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
   a non-canonical form, raise the SS exception.</p>"

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* (((when (app-view x86))
        (!!ms-fresh :lidt-unimplemented))

       ;; If the current privilege level is not 0, the #GP exception is
       ;; raised. This is handled during dispatch --- see opcode-maps for
       ;; details.

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((the (integer 4 8) base-size)
        (if (64-bit-modep x86) 8 4))

       ((the (integer 6 10) base-size+2) (+ 2 base-size))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0
            mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode 0
                                                base-size+2
                                                inst-ac?
                                                t ;; Memory pointer operand
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; The operand size attribute is needed because, according to Intel
       ;; manual, May'18, specification of LGDT, only 24 bits from the base are
       ;; copied into GDTR when the operand size attribute is 16 bits.
       (p3? (eql #.*operand-size-override* (prefixes->opr prefixes)))
       (operand-size
        (if (eql base-size 8)
            8
          (b* (((the (unsigned-byte 16) cs-attr)
                (xr :seg-hidden-attr #.*cs* x86))
               (cs.d
                (code-segment-descriptor-attributesBits->d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))
       (base-bits (case operand-size
                    (8 64)
                    (4 32)
                    (t 24)))

       ;; Load the memory operand in the IDTR register.
       (idtr-limit
        (!gdtr/idtrBits->limit
                                 (part-select mem :low 0 :width 16)
                                 0))
       (idtr
        (!gdtr/idtrBits->base-addr
                                 (part-select mem :low 16 :width base-bits)
                                 idtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *idtr* idtr x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LLDT
;; ======================================================================

(def-inst x86-lldt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
                                         riml32
                                         ia32e-valid-ldt-segment-descriptor-p
                                         ;; [Shilpi] Should probably also have
                                         ;; linear rules about the following...
                                         system-segment-descriptorBits->base15-0
                                         system-segment-descriptorBits->base23-16
                                         system-segment-descriptorBits->base31-24
                                         system-segment-descriptorBits->base63-32
                                         system-segment-descriptorbits->limit15-0
                                         system-segment-descriptorbits->limit19-16)
                                        ())))

  :long "<h3>Op/En = M: \[OP r/m16\]</h3>
  \[OP  M\]<br/>
  0F 00/2: LLDT r/m16<br/>

  <p>If bits 2-15 of the source operand are 0, LDTR is marked invalid
and the LLDT instruction completes silently. However, all subsequent
references to descriptors in the LDT (except by the LAR, VERR, VERW or
LSL instructions) cause a general protection exception.</p>

<p>The operand-size attribute has no effect on this instruction. In
64-bit mode, the operand size is fixed at 16 bits.</p>

<p><b>TO-DO:</b> If a memory address referencing the SS segment is in
a non-canonical form, raise the SS exception.</p>"

  :prepwork

  ((local (in-theory (e/d* (lldt-guard-helpers) ()))))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* (((when (app-view x86))
        (!!ms-fresh :lldt-unimplemented))

       ;; If the current privilege level is not 0, the #GP exception is
       ;; raised. This is handled during dispatch --- see opcode-maps for
       ;; details.

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0
            selector
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                0
                                                2
                                                inst-ac?
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

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Getting the selector's components:
       ((the (unsigned-byte 13) sel-index)
        (segment-selectorBits->index selector))
       ((the (unsigned-byte 1) sel-ti)
        (segment-selectorBits->ti selector))
       ((the (unsigned-byte 2) sel-rpl)
        (segment-selectorBits->rpl selector))

       ;; Determining whether the selector is valid...

       ;; Does the selector point to the GDT?
       ((when (equal sel-ti 1))
        (!!ms-fresh :gp-selector-does-not-point-to-GDT selector))

       ;; Is the limit of the selector within the GDTR limit?
       ;; Getting the GDTR base and limit
       ;; (in 32-bit mode, we take the low 32 bits of the base address):
       ((the (unsigned-byte 80) gdtr)
        (stri *gdtr* x86))
       ((the (unsigned-byte 64) gdtr-base)
        (if (eql proc-mode #.*64-bit-mode*)
            (gdtr/idtrBits->base-addr gdtr)
          (n32 (gdtr/idtrBits->base-addr gdtr))))
       ((the (unsigned-byte 16) gdtr-limit)
        (gdtr/idtrBits->limit gdtr))
       ;; Source: Intel Vol. 3A, Section 3.5.1:
       ;; "The limit value for the GDT is expressed in bytes. As with
       ;; segments, the limit value is added to the base address to
       ;; get the address of the last valid byte. A limit value of 0
       ;; results in exactly one valid byte. Because segment descrip-
       ;; tors are always 8 bytes long, the GDT limit should always be
       ;; one less than an integral multiple of eight (that is, 8N - 1)."
       ;; To obtain the largest address of the descriptor that we are reading
       ;; from the GDT, we multiply the selector index by 8 and we add either 7
       ;; or 15 to it, depending on whether we are in 32-bit or 64-bit mode,
       ;; because in 32-bit mode the descriptor is 8 bytes long (see AMD
       ;; manual, Dec'17, Volume 2, Figure 4-16), while in 64-bit mode the
       ;; descriptor is 16 bytes long (see AMD manual, Dec'17, Volume 2, Figure
       ;; 4-22).
       (largest-address (+ (ash sel-index 3)
                           (if (eql proc-mode *64-bit-mode*) 15 7)))
       ((when (< gdtr-limit largest-address))
        (!!ms-fresh :gp-selector-limit-check-failed (cons selector gdtr)))

       ;; Is the selector a null selector?  A null selector points to
       ;; the first entry in the GDT (sel-index=0, ti=0).

       ;; Source: Intel Vol. 2A, Instruction Set Reference (LLDT):
       ;; "LDTR is marked invalid and the LLDT instruction completes
       ;; silently. However, all subsequent references to descriptors
       ;; in the LDT (except by the LAR, VERR, VERW or LSL
       ;; instructions) cause a general protection exception (#GP)."

       ;; [Shilpi]: I believe that when the manuals tell us to mark
       ;; the LDTR invalid, we just have to load the selector into the
       ;; visible portion of LDTR and leave the hidden portion
       ;; unmodified.
       ((when (equal sel-index 0))
        (let* ((x86 (!ssr-visiblei *ldtr* selector x86)))
          x86))

       ;; Now that we know the segment selector is valid, we check if
       ;; the segment descriptor is valid.

       (descriptor-addr
        ;; The index is scaled by 8.
        (+ gdtr-base (the (unsigned-byte 16) (ash sel-index 3))))
       ((when (not (canonical-address-p descriptor-addr)))
        (!!ms-fresh :descriptor-addr-virtual-memory-error descriptor-addr))

       ;; The descriptor is 16 bytes in 64-bit mode, 8 bytes in 32-bit mode.
       (descriptor-size (if (eql proc-mode *64-bit-mode*) 16 8))
       ((mv flg (the (unsigned-byte 128) descriptor) x86)
        ;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
        (rml-size descriptor-size descriptor-addr :x x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))

       ((mv descriptor-valid? reason)
        ;; This predicate is also adequate to check the validity of 8-byte
        ;; descriptors in 32-bit mode, because their high 8 bytes are all 0.
        (ia32e-valid-ldt-segment-descriptor-p descriptor))
       ((when (not descriptor-valid?))
        (!!ms-fresh :invalid-segment-descriptor reason))

       ;; LDTR Base (note the high 32 bits are 0 in 32-bit mode):
       (ldtr-base15-0  (system-segment-descriptorBits->base15-0  descriptor))
       (ldtr-base23-16 (system-segment-descriptorBits->base23-16 descriptor))
       (ldtr-base31-24 (system-segment-descriptorBits->base31-24 descriptor))
       (ldtr-base63-32 (system-segment-descriptorBits->base63-32 descriptor))
       ((the (unsigned-byte 40) ldtr-base63-24)
        (part-install ldtr-base31-24
                      (ash ldtr-base63-32 8)
                      :low 0 :width 8))
       ((the (unsigned-byte 24) ldtr-base23-0)
        (part-install ldtr-base15-0 (ash ldtr-base23-16 16)
                      :low 0 :width 16))
       ((the (unsigned-byte 64) ldtr-base)
        (part-install ldtr-base23-0 (ash ldtr-base63-24 24)
                      :low 0 :width 24))

       ;; LDTR Limit:
       (ldtr-limit15-0  (system-segment-descriptorBits->limit15-0
                         descriptor))
       (ldtr-limit19-16 (system-segment-descriptorBits->limit19-16
                         descriptor))
       ((the (unsigned-byte 32) ldtr-limit)
        (part-install ldtr-limit15-0
                      (ash ldtr-limit19-16 16)
                      :low 0 :width 16))

       ;; LDTR Attributes:
       (ldtr-attr (the (unsigned-byte 16)
                    (make-system-segment-attr-field descriptor)))
       ;; Update the x86 state:
       ;; Load the visible and hidden portions of the LDTR register:
       (x86 (!ssr-visiblei #.*ldtr* selector x86))
       (x86 (!ssr-hidden-basei #.*ldtr* ldtr-base x86))
       (x86 (!ssr-hidden-limiti #.*ldtr* ldtr-limit x86))
       (x86 (!ssr-hidden-attri #.*ldtr* ldtr-attr x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
