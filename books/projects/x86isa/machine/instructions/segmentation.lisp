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

  :long "<h3>Op/En = M: \[OP m16@('&')m64\]</h3>

  <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
  bytes (an 8-byte base and a 2-byte limit).</p>

  <p>\[OP  M\]<br/>
  0F 01/2: LGDT m16@('&')64</p>

  <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
  a non-canonical form, raise the SS exception.</p>"

  :implemented
  (add-to-implemented-opcodes-table 'LGDT #x0F01 '(:reg 2)
                                    'x86-lgdt)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lgdt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cpl (cpl x86))
       ((when (not (equal cpl 0)))
        (!!ms-fresh :cpl-not-zero cpl))
       ;; If the source operand is not a memory location, then #GP is
       ;; raised.
       ((when (equal mod #b11))
        (!!ms-fresh :source-operand-not-memory-location mod))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0 mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         0 10 inst-ac?
         t ;; Memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Load the memory operand in the GDTR register.
       (gdtr-limit
        (!gdtr/idtr-layout-slice :limit
                                 (part-select mem :low 0 :width 16)
                                 0))
       (gdtr
        (!gdtr/idtr-layout-slice :base-addr
                                 (part-select mem :low 16 :width 64)
                                 gdtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *gdtr* gdtr x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LIDT
;; ======================================================================

(def-inst x86-lidt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :long "<h3>Op/En = M: \[OP m16@('&')m64\]</h3>

  <p>In 64-bit mode, the instruction's operand size is fixed at 8+2
  bytes (an 8-byte base and a 2-byte limit).</p>

  <p>\[OP  M\]<br/>
  0F 01/3: LIDT m16@('&')64</p>

  <p><b>TO-DO:</b> If a memory address referencing the SS segment is in
  a non-canonical form, raise the SS exception.</p>"

  :implemented
  (add-to-implemented-opcodes-table 'LIDT #x0F01 '(:reg 3)
                                    'x86-lidt)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lidt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cpl (cpl x86))
       ((when (not (equal cpl 0)))
        (!!ms-fresh :cpl-not-zero cpl))
       ;; If the source operand is not a memory location, then #GP is
       ;; raised.
       ((when (equal mod #b11))
        (!!ms-fresh :source-operand-not-memory-location mod))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0 mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         0 10 inst-ac?
         t ;; Memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Load the memory operand in the IDTR register.
       (idtr-limit
        (!gdtr/idtr-layout-slice :limit
                                 (part-select mem :low 0 :width 16)
                                 0))
       (idtr
        (!gdtr/idtr-layout-slice :base-addr
                                 (part-select mem :low 16 :width 64)
                                 idtr-limit))

       ;; Update the x86 state:
       (x86 (!stri *idtr* idtr x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LLDT
;; ======================================================================

(def-inst x86-lldt

  :parents (privileged-opcodes two-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08
                                         riml32
                                         ia32e-valid-ldt-segment-descriptor-p)
                                        ())))
  :implemented
  (add-to-implemented-opcodes-table 'LLDT #x0F00 '(:reg 2) 'x86-lldt)

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

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((ctx 'x86-lldt)
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; If the current privilege level is not 0, the #GP exception
       ;; is raised.
       (cpl (cpl x86))
       ((when (not (equal cpl 0)))
        (!!ms-fresh :cpl-not-zero cpl))
       ;; If the lock prefix is used, then the #UD exception is
       ;; raised.
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))

       ;; Fetch the memory operand:
       (inst-ac? nil)
       ((mv flg0 selector (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         0 2 inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Getting the selector's components:
       ((the (unsigned-byte 13) sel-index)
        (seg-sel-layout-slice :index selector))
       ((the (unsigned-byte 1) sel-ti)
        (seg-sel-layout-slice :ti selector))
       ((the (unsigned-byte 2) sel-rpl)
        (seg-sel-layout-slice :rpl selector))

       ;; Determining whether the selector valid...

       ;; Does the selector point to the GDT?
       ((when (equal sel-ti 1))
        (!!ms-fresh :gp-selector-does-not-point-to-GDT selector))

       ;; Is the limit of the selector within the GDTR limit?
       ;; Getting the GDTR base and limit:
       ((the (unsigned-byte 80) gdtr)
        (stri *gdtr* x86))
       ((the (unsigned-byte 64) gdtr-base)
        (gdtr/idtr-layout-slice  :base-addr gdtr))
       ((the (unsigned-byte 16) gdtr-limit)
        (gdtr/idtr-layout-slice :limit gdtr))
       ;; Source: Intel Vol. 3A, Section 3.5.1:
       ;; "The limit value for the GDT is expressed in bytes. As with
       ;; segments, the limit value is added to the base address to
       ;; get the address of the last valid byte. A limit value of 0
       ;; results in exactly one valid byte. Because segment descrip-
       ;; tors are always 8 bytes long, the GDT limit should always be
       ;; one less than an integral multiple of eight (that is, 8N
       ;; 1)."
       ((when (< gdtr-limit sel-index))
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

       ((mv flg (the (unsigned-byte 128) descriptor) x86)
        ;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
        (rml-size 16 descriptor-addr :x x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))

       ((mv descriptor-valid? reason)
        (ia32e-valid-ldt-segment-descriptor-p descriptor))
       ((when (not descriptor-valid?))
        (!!ms-fresh :invalid-segment-descriptor reason))

       ;; LDTR Base:
       (ldtr-base15-0  (system-segment-descriptor-layout-slice :base15-0  descriptor))
       (ldtr-base23-16 (system-segment-descriptor-layout-slice :base23-16 descriptor))
       (ldtr-base31-24 (system-segment-descriptor-layout-slice :base31-24 descriptor))
       (ldtr-base63-32 (system-segment-descriptor-layout-slice :base63-32 descriptor))
       ((the (unsigned-byte 40) ldtr-base63-24)
        (part-install
         ldtr-base31-24
         (ash ldtr-base63-32 8)
         :low 0 :width 8))
       ((the (unsigned-byte 24) ldtr-base23-0)
        (part-install ldtr-base15-0
                      (ash ldtr-base23-16 16)
                      :low 0 :width 16))
       ((the (unsigned-byte 64) ldtr-base)
        (part-install ldtr-base23-0
                      (ash ldtr-base63-24 24)
                      :low 0 :width 24))

       ;; LDTR Limit:
       (ldtr-limit15-0  (system-segment-descriptor-layout-slice :limit15-0   descriptor))
       (ldtr-limit19-16 (system-segment-descriptor-layout-slice :limit19-16  descriptor))
       (ldtr-limit      (part-install ldtr-limit15-0
                                      (ash ldtr-limit19-16 16)
                                      :low 0 :width 16))

       ;; LDTR Attributes:
       (ldtr-attr (the (unsigned-byte 16)
                    (make-system-segment-attr-field descriptor)))

       ;; LDTR Hidden:
       (ldtr-hidden
        (!hidden-seg-reg-layout-slice
         :base-addr
         ldtr-base
         (!hidden-seg-reg-layout-slice
          :limit
          ldtr-limit
          (!hidden-seg-reg-layout-slice
           :attr
           ldtr-attr
           0))))

       ;; Update the x86 state:
       ;; Load the visible and hidden portions of the LDTR register:
       (x86
        (!ssr-visiblei *ldtr* selector x86))
       (x86
        (!ssr-hiddeni *ldtr* ldtr-hidden x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
