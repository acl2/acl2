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
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================
;; INSTRUCTION: (one-byte opcode map)
;; jmp
;; ======================================================================

; From Intel Vol. 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET, JCC,
;; JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions update the
;; 64-bit RIP without the need for a REX operand-size prefix.

;; The following aspects of near branches are controlled by the effective
;; operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits regardless of
;; operand size prefixes (operand size prefixes are silently ignored). However,
;; the displacement field for relative branches is still limited to 32 bits and
;; the address size for near branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they also
;; impact the address calculation for memory indirect branches. Such addresses
;; are 64 bits by default; but they can be overridden to 32 bits by an address
;; size prefix.

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-near-jmp-Op/En-D

  ;; Op/En: D
  ;; E9: JMP rel32: Jump Near, relative, RIP = RIP + 32-bit
  ;;                displacement sign-extended to 64-bits
  ;; EB: JMP rel8: Jump Short, RIP = RIP + 8-bit displacement
  ;;                sign-extended to 64-bits

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (rime-size-of-1-to-rime08
                                         rime-size-of-2-to-rime16
                                         rime-size-of-4-to-rime32)
                                        ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'JMP #xE9 '(:nil nil)
                                      'x86-near-jmp-Op/En-D)
    (add-to-implemented-opcodes-table 'JMP #xEB '(:nil nil)
                                      'x86-near-jmp-Op/En-D))

  :body

  (b* ((ctx 'x86-near-jmp-Op/En-D)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 0 4) offset-size)
        (if (eql opcode #xEB) ; jump short
            1 ; always 8 bits (rel8)
          ;; opcode = #xE9 -- jump near relative:
          (if (64-bit-modep x86)
              4 ; always 32 bits (rel32) -- 16 bits (rel16) not supported
            (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                 (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
                 (cs.d (code-segment-descriptor-attributes-layout-slice
                        :d cs-attr)))
              (if (= cs.d 1)
                  (if p3? 2 4) ; 16 or 32 bits (rel16 or rel32)
                (if p3? 4 2))))))

       ((mv ?flg (the (signed-byte 32) offset) x86)
        (rime-size offset-size temp-rip *cs* :x nil x86))
       ((when flg) (!!ms-fresh :rime-size-error flg))

       ((mv flg next-rip)
        (add-to-*ip temp-rip (the (integer 0 4) offset-size) x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg temp-rip) (add-to-*ip next-rip offset x86))
       ((when flg) (!!ms-fresh :virtual-memory-error temp-rip))

       ;; when the size is 16 bits, zero the high bits of EIP
       ;; (see pseudocode of JMP in Intel manual, Mar'17, Vol. 2:
       (temp-rip (if (eql offset-size 2)
                     (logand #xffff temp-rip)
                   temp-rip))

       ;; Update the x86 state:
       (x86 (write-*ip temp-rip x86)))
    x86))

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-near-jmp-Op/En-M

  ;; Absolute indirect jump: RIP = r/m16/32/64
  ;; FF/4: JMP r/m16
  ;; FF/4: JMP r/m32
  ;; FF/4: JMP r/m64
  ;; Op/En: M

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'JMP #xFF '(:reg 4)
                                    'x86-near-jmp-Op/En-M)

  :body

  (b* ((ctx 'x86-near-jmp-Op/En-M)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 4 when this
       ;; function is called.
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 2 8) operand-size)
        (if (64-bit-modep x86)
            8 ; Intel manual, Mar'17, Volume 1, Section 6.3.7
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d (code-segment-descriptor-attributes-layout-slice
                      :d cs-attr)))
            (if (= cs.d 1)
                (if p3? 2 4)
              (if p3? 4 2)))))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg
            jmp-addr
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes$ #.*gpr-access*
                                                operand-size
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
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Note that instruction pointers are modeled as signed in 64-bit mode,
       ;; but unsigned in 32-bit mode.
       (jmp-addr (if (64-bit-modep x86)
                     (i64 jmp-addr)
                   jmp-addr))
       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). See pseudocode in Intel
       ;; manual.
       ((unless (if (64-bit-modep x86)
                    (canonical-address-p jmp-addr)
                  (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                       (cs.limit (hidden-seg-reg-layout-slice :limit cs-hidden)))
                    (and (<= 0 jmp-addr) (<= jmp-addr cs.limit)))))
        (!!fault-fresh :gp 0 :bad-return-address jmp-addr)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (write-*ip jmp-addr x86)))
      x86))

(local
 (defthm unsigned-byte-p-128-xr-str
   (implies (x86p x86)
            (unsigned-byte-p 128 (xr :str i x86)))))

(def-inst x86-far-jmp-Op/En-D

  :parents (one-byte-opcodes)
  :short "Absolute Indirect Jump: Far"
  :long "<p>Op/En: D</p>
<p><tt>FF/5: JMP m16:16 or m16:32 or m16:64</tt></p>

<p>Source: Intel Manuals \(Vol. 2A\) Instruction Set Reference: the
text below has been edited to contain information only about the
64-bit mode.</p>

<p><i>The JMP instruction cannot be used to perform
inter-privilege-level far jumps.</i> The processor always uses the
segment selector part of the far address to access the corresponding
descriptor in the GDT or LDT. The descriptor type and access rights
determine the type of jump to be performed.</p>

<p><b>Far Jump to a Conforming or Non-Conforming Code Segment:</b> If
the selected descriptor is for a code segment, a far jump to a code
segment at the same privilege level is performed. If the selected code
segment is at a different privilege level and the code segment is
non-conforming, a general-protection exception is generated.  The
target operand specifies an absolute far address indirectly with a
memory location \(m16:16 or m16:32 or m16:64\). The operand-size
attribute and the REX.w bit determine the size of the offset \(16 or
32 or 64 bits\) in the far address. The new code segment selector and
its descriptor are loaded into CS register, and the offset from the
instruction is loaded into the RIP register.</p>

<p><b>Far Jump through a Call Gate:</b> When executing a far jump
through a call gate, the segment selector specified by the target
operand identifies the call gate. The offset part of the target
operand is ignored. The processor then jumps to the code segment
specified in the call gate descriptor and begins executing the
instruction at the offset specified in the call gate. No stack switch
occurs. The target operand specifies the far address of the call gate
indirectly with a memory location \(m16:16 or m16:32 or m16:64\).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d* ()
                                                 (unsigned-byte-p
                                                  member-equal
                                                  acl2::logtail-identity
                                                  not rml-size
                                                  signed-byte-p
                                                  select-operand-size)))))
  :implemented
  (add-to-implemented-opcodes-table 'JMP #xFF '(:reg 5)
                                    'x86-far-jmp-Op/En-D)

  :prepwork
  ((local (in-theory (e/d* (far-jump-guard-helpers)
                           (unsigned-byte-p
                            member-equal
                            acl2::logtail-identity
                            not
                            signed-byte-p)))))
  :body

  (b* ((ctx 'x86-far-jmp-Op/En-M)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))

       ;; Note that this exception was not mentioned in the Intel
       ;; Manuals, but I think that the reason for this omission was
       ;; that the JMP instruction reference sheet mentioned direct
       ;; addressing opcodes too (which are unavailable in the 64-bit
       ;; mode).  If the source operand is not a memory location, then
       ;; #GP(0) is raised.
       ((when (equal mod #b11))
        (!!ms-fresh :source-operand-not-memory-location mod))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (offset-size
        ;; Offset size can be 2, 4, or 8 bytes.
        (select-operand-size nil rex-byte nil prefixes x86))

       (seg-reg (select-segment-register p2 p4? mod r/m x86))

       (inst-ac? t)
       ((mv flg
            mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes$
         #.*gpr-access*
         ;; offset-size is the number of bytes of the
         ;; offset.  We need two more bytes for the selector.
         (the (integer 2 10) (+ 2 offset-size))
         inst-ac?
         t ;; A memory pointer operand
         seg-reg
         p4?
         temp-rip
         rex-byte
         r/m
         mod
         sib
         0 ;; No immediate operand
         x86))
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes-error flg))

       (badlength?
        (check-instruction-length start-rip temp-rip increment-RIP-by))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (selector (the (unsigned-byte 16) (n16 mem)))
       (offset (mbe :logic (part-select mem :low 16 :width
                                        (ash offset-size 3))
                    :exec (ash mem -16)))

       ;; Getting the selector's components:
       ((the (unsigned-byte 13) sel-index)
        (seg-sel-layout-slice :index selector))
       ((the (unsigned-byte 1) sel-ti)
        (seg-sel-layout-slice :ti selector))
       ((the (unsigned-byte 2) sel-rpl)
        (seg-sel-layout-slice :rpl selector))

       ;; Is the selector a null selector?  A null selector points to
       ;; the first entry in the GDT (sel-index=0, ti=0).
       ;; The exception #GP(0) is raised when the segment selector in
       ;; the destination operand is NULL.
       ((when (and (equal sel-ti 0)
                   (equal sel-index 0)))
        (!!fault-fresh :gp 0 :gp-nullselector 0)) ;; #GP(0)

       ((mv dt-base-addr dt-limit)
        (if (equal sel-ti 0)
            ;; Selector references the GDT.
            (b* ((gdtr (the (unsigned-byte 80) (stri *gdtr* x86)))
                 (gdtr-base (gdtr/idtr-layout-slice :base-addr gdtr))
                 (gdtr-limit (gdtr/idtr-layout-slice :limit gdtr)))
              (mv gdtr-base gdtr-limit))
          ;; Selector references the LDT whose base address is in
          ;; LDTR.
          (b* ((ldtr-hidden (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86)))
               (ldtr-base (hidden-seg-reg-layout-slice :base-addr ldtr-hidden))
               (ldtr-limit (hidden-seg-reg-layout-slice :limit ldtr-hidden)))
            (mv ldtr-base ldtr-limit))))

       ;; Is the limit of the selector within the descriptor table
       ;; limit?
       ;; The exception #GP(selector) is raised when offset is beyond
       ;; the code segment limit.
       ((when (< dt-limit sel-index))
        (!!fault-fresh
         :gp sel-index ;; #GP(selector)
         :gp-selector-limit-check-failed (list selector dt-base-addr dt-limit)))

       ;; Now that we know the segment selector is valid, we check if
       ;; the segment descriptor is valid.
       (descriptor-addr
        ;; The index is scaled by 8.
        (+ dt-base-addr (the (unsigned-byte 16) (ash sel-index 3))))
       ((when (not (canonical-address-p descriptor-addr)))
        (!!ms-fresh :descriptor-addr-virtual-memory-error descriptor-addr))

       ;; Note that the code or data segment descriptors are 8 bytes
       ;; wide but all other descriptors are 16 bytes wide in the
       ;; 64-bit mode.
       ((mv flg (the (unsigned-byte 128) descriptor) x86)
        ;; [TO-DO@Shilpi]: I believe I should use :x below and not
        ;; :r. Double check.
        (rml-size 16 descriptor-addr :x x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))

       ;; If segment type is neither a code segment (conforming or
       ;; non-conforming) nor a call gate, then #GP(selector) is
       ;; raised.
       ((mv flg code-or-call-gate? descriptor)
        (b* ((descriptor-64 (n64 descriptor))
             ((mv valid? reason1)
              ;; Note that the following predicate reports the
              ;; descriptor to be invalid if the P flag of the
              ;; descriptor is 0.
              (ia32e-valid-code-segment-descriptor-p descriptor-64))
             ((when valid?)
              (mv nil 0 descriptor-64))
             ((mv valid? reason2)
              ;; Note that the following predicate reports the
              ;; descriptor to be invalid if the P flag of the
              ;; descriptor is 0.
              (ia32e-valid-call-gate-segment-descriptor-p descriptor))
             ((when valid?)
              (mv nil 1 descriptor)))
          (mv t (cons reason1 reason2) descriptor)))
       ((when flg)
        (!!ms-fresh
         :either-both-code-segment-or-call-gate-are-absent-or-some-other-descriptor-is-present
         (cons code-or-call-gate? descriptor))))

    (if (eql code-or-call-gate? 0) ;; Code Segment:

        (if (equal (code-segment-descriptor-layout-slice :c descriptor)
                   1)

            ;; Conforming Code Segment:

            (b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
                 (cpl (seg-sel-layout-slice :rpl current-cs-register))
                 (dpl (code-segment-descriptor-layout-slice
                       :dpl descriptor))
                 ;; Access is allowed to a conforming code segment
                 ;; when DPL <= CPL (numerically).  RPL is ignored
                 ;; for this privilege check.  If access is not
                 ;; allowed, #GP(segment-selector) is raised.
                 ((when (not (<= dpl cpl)))
                  (!!fault-fresh
                   :gp sel-index ;; #GP(selector)
                   :privilege-check-fail (acons :dpl dpl
                                           (acons :cpl cpl nil))))

                 ;; Trimming the offset based on the operand-size:
                 (jmp-addr
                  (case offset-size
                    (2 (n16 offset))
                    (4 (n32 offset))
                    (t offset)))

                 ;; #GP(0) is thrown if the target offset in destination is
                 ;; non-canonical.
                 ((when (not (canonical-address-p jmp-addr)))
                  (!!fault-fresh
                   :gp 0 :target-offset-virtual-memory-error jmp-addr)) ;; #GP(0)

                 (new-cs-visible
                  (!seg-sel-layout-slice :rpl cpl selector))

                 (new-cs-hidden
                  (if (equal sel-ti 1)
                      ;; Load the hidden portions of the CS segment
                      ;; from the LDTR's hidden portion.
                      (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
                    ;; Descriptor was in GDT.
                    (!hidden-seg-reg-layout-slice
                     :base-addr dt-base-addr
                     (!hidden-seg-reg-layout-slice
                      :limit dt-limit
                      (!hidden-seg-reg-layout-slice
                       ;; Get attributes from the descriptor in GDT.
                       :attr (make-code-segment-attr-field descriptor)
                       0)))))

                 ;; Update x86 state:
                 (x86 (!seg-visiblei *cs* new-cs-visible x86))
                 (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
                 (x86 (write-*ip jmp-addr x86)))
              x86)

          ;; Non-Conforming Code Segment:

          (b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
               (cpl (seg-sel-layout-slice :rpl current-cs-register))
               (dpl (code-segment-descriptor-layout-slice
                     :dpl descriptor))
               ;; Access is allowed to a conforming code segment
               ;; when RPL <= CPL (numerically) and CPL = DPL. If
               ;; access is not allowed, #GP(segment-selector) is
               ;; raised.
               ((when (not (and (<= sel-rpl cpl)
                                (equal cpl dpl))))
                (!!fault-fresh
                 :gp sel-index ;; #GP(selector)
                 :privilege-check-fail (acons :dpl dpl
                                         (acons :cpl cpl
                                           (acons :rpl sel-rpl nil)))))

               ;; Trimming the offset based on the operand-size:
               (jmp-addr
                (case offset-size
                  (2 (n16 offset))
                  (4 (n32 offset))
                  (t offset)))

               ;; #GP(0) is thrown if the target offset in destination is
               ;; non-canonical.
               ((when (not (canonical-address-p jmp-addr)))
                (!!ms-fresh :target-offset-virtual-memory-error jmp-addr))

               (new-cs-visible
                (!seg-sel-layout-slice :rpl cpl selector))

               (new-cs-hidden
                (if (equal sel-ti 1)
                    ;; Load the hidden portions of the CS segment
                    ;; from the LDTR's hidden portion.
                    (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
                  ;; Descriptor was in GDT.
                  (!hidden-seg-reg-layout-slice
                   :base-addr dt-base-addr
                   (!hidden-seg-reg-layout-slice
                    :limit dt-limit
                    (!hidden-seg-reg-layout-slice
                     ;; Get attributes from the descriptor in GDT.
                     :attr (make-code-segment-attr-field descriptor)
                     0)))))

               ;; Update x86 state:
               (x86 (!seg-visiblei *cs* new-cs-visible x86))
               (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
               (x86 (write-*ip jmp-addr x86)))
            x86))

      ;; Call Gate Descriptor:

      (b* ((current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
           (cpl (seg-sel-layout-slice :rpl current-cs-register))
           (dpl (call-gate-descriptor-layout-slice :dpl descriptor))

           ;; Access is allowed when:
           ;; 1. CPL <= Call gate's DPL
           ;; 2. RPL <= Call gate's DPL
           ;; 3. If the destination Code segment is conforming,
           ;;    then: DPL of code segment <= CPL
           ;;    If the destination Code segment is non-conforming,
           ;;    then: DPL of code segment = CPL.
           ;; If access is not allowed, #GP(segment-selector) is
           ;; raised.
           ;; Below, we check 1 and 2.  We will check for 3 after we
           ;; read in the code segment descriptor.
           ((when (not (and (<= cpl dpl)
                            (<= sel-rpl dpl))))
            (!!ms-fresh :privilege-check-fail
                        (acons :dpl dpl
                               (acons :cpl cpl
                                      (acons :rpl sel-rpl nil)))))

           (cs-selector
            (call-gate-descriptor-layout-slice :selector descriptor))
           ((the (unsigned-byte 13) cs-sel-index)
            (seg-sel-layout-slice :index cs-selector))
           ((the (unsigned-byte 1) cs-sel-ti)
            (seg-sel-layout-slice :ti cs-selector))
           ((the (unsigned-byte 2) cs-sel-rpl)
            (seg-sel-layout-slice :rpl cs-selector))

           ;; If the call gate's code segment selector is NULL,
           ;; #GP(0) is raised.
           ((when (and (equal cs-sel-ti 0)
                       (equal cs-sel-index 0)))
            (!!ms-fresh :call-gate-code-segment-nullselector 0))

           ;; Is the call gate code segment selector index outside
           ;; the descriptor table limit?  If so, #GP(code segment
           ;; selector) is raised.
           ((mv cs-dt-base-addr cs-dt-limit)
            (if (equal sel-ti 0)
                ;; Code Segment Selector references the GDT.
                (b* ((gdtr (the (unsigned-byte 80) (stri *gdtr* x86)))
                     (gdtr-base (gdtr/idtr-layout-slice :base-addr gdtr))
                     (gdtr-limit (gdtr/idtr-layout-slice :limit gdtr)))
                  (mv gdtr-base gdtr-limit))
              ;; Code Segment Selector references the LDT whose base
              ;; address is in LDTR.
              (b* ((ldtr-hidden (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86)))
                   (ldtr-base (hidden-seg-reg-layout-slice :base-addr ldtr-hidden))
                   (ldtr-limit (hidden-seg-reg-layout-slice :limit ldtr-hidden)))
                (mv ldtr-base ldtr-limit))))
           ((when (< cs-dt-limit cs-sel-index))
            (!!ms-fresh :gp-selector-limit-check-failed
                        (list cs-selector cs-dt-base-addr cs-dt-limit)))

           ;; Reading the code segment: we check if the code segment
           ;; descriptor is valid.
           (cs-descriptor-addr
            ;; The index is scaled by 8.
            (+ cs-dt-base-addr (the (unsigned-byte 16) (ash cs-sel-index 3))))
           ((when (not (canonical-address-p cs-descriptor-addr)))
            (!!ms-fresh :cs-descriptor-addr-virtual-memory-error cs-descriptor-addr))
           ((mv flg (the (unsigned-byte 64) cs-descriptor) x86)
            ;; [TO-DO@Shilpi]: I believe I should use :x below and not :r.
            (rml-size 8 cs-descriptor-addr :x x86))
           ((when flg)
            (!!ms-fresh :rml-size-error flg))
           ((mv valid? reason)
            ;; Note that the following predicate reports the
            ;; descriptor to be invalid if the P flag of the
            ;; descriptor is 0.
            (ia32e-valid-code-segment-descriptor-p cs-descriptor))
           ((when (not valid?))
            (!!ms-fresh :call-gate-code-segment-descriptor-invalid
                        (cons reason cs-descriptor)))

           ;; Checking the privileges of the code segment:
           (cs-dpl (code-segment-descriptor-layout-slice :dpl cs-descriptor))
           (c-bit (code-segment-descriptor-layout-slice :c cs-descriptor))
           ((when (or (and ;; Conforming code segment
                       (equal c-bit 1)
                       (not (<= cs-dpl cpl)))
                      (and ;; Conforming code segment
                       (equal c-bit 0)
                       (not (eql cs-dpl cpl)))))
            (!!ms-fresh :privilege-check-fail
                        (acons :c-bit c-bit
                               (acons :cpl cpl
                                      (acons :cs-dpl cs-dpl nil)))))

           (call-gate-offset15-0
            (call-gate-descriptor-layout-slice :offset15-0 descriptor))
           (call-gate-offset31-16
            (call-gate-descriptor-layout-slice :offset31-16 descriptor))
           (call-gate-offset63-32
            (call-gate-descriptor-layout-slice :offset63-32 descriptor))
           (call-gate-offset31-0
            (mbe :logic (part-install call-gate-offset15-0
                                      (ash call-gate-offset31-16 16)
                                      :low 0 :width 16)
                 :exec
                 (the (unsigned-byte 32)
                   (logior (the (unsigned-byte 16) call-gate-offset15-0)
                           (the (unsigned-byte 32) (ash call-gate-offset31-16 16))))))
           (call-gate-offset
            (mbe :logic
                 (part-install call-gate-offset31-0
                               (ash call-gate-offset63-32 32)
                               :low 0 :width 32)
                 :exec
                 (the (unsigned-byte 64)
                   (logior (the (unsigned-byte 32) call-gate-offset31-0)
                           (the (unsigned-byte 64) (ash call-gate-offset63-32 32))))))

           ;; Trimming the call gate offset based on the operand-size:
           (jmp-addr
            (case offset-size
              (2 (n16 call-gate-offset))
              (4 (n32 call-gate-offset))
              (t call-gate-offset)))

           ;; #GP(0) is thrown if the target offset in destination is
           ;; non-canonical.
           ((when (not (canonical-address-p jmp-addr)))
            (!!ms-fresh :target-offset-virtual-memory-error jmp-addr))

           (new-cs-visible
            (!seg-sel-layout-slice :rpl cpl cs-selector))

           (new-cs-hidden
            (if (equal cs-sel-ti 1)
                ;; Load the hidden portions of the CS segment
                ;; from the LDTR's hidden portion.
                (the (unsigned-byte 112) (ssr-hiddeni *ldtr* x86))
              ;; Descriptor was in GDT.
              (!hidden-seg-reg-layout-slice
               :base-addr cs-dt-base-addr
               (!hidden-seg-reg-layout-slice
                :limit cs-dt-limit
                (!hidden-seg-reg-layout-slice
                 ;; Get attributes from the descriptor in GDT.
                 :attr (make-code-segment-attr-field cs-descriptor)
                 0)))))

           ;; Update x86 state:
           (x86 (!seg-visiblei *cs* new-cs-visible x86))
           (x86 (!seg-hiddeni  *cs* new-cs-hidden  x86))
           (x86 (!rip jmp-addr x86)))
        x86))))

;; ======================================================================
;; INSTRUCTION: LOOP
;; ======================================================================

; From Intel Vol. 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET, JCC,
;; JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions update the
;; 64-bit RIP without the need for a REX operand-size prefix.

;; The following aspects of near branches are controlled by the effective
;; operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits regardless of
;; operand size prefixes (operand size prefixes are silently ignored). However,
;; the displacement field for relative branches is still limited to 32 bits and
;; the address size for near branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they also
;; impact the address calculation for memory indirect branches. Such addresses
;; are 64 bits by default; but they can be overridden to 32 bits by an address
;; size prefix.

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-loop

  ;; E0: LOOPNE/LOOPNZ rel8
  ;; E1: LOOPE/LOOPZ rel8
  ;; E2: LOOP rel8

  ;; Intel Vol2A, LOOP/LOOPcc specification says:
  ;; "Performs the loop operation using the RCX, ECX or CX as a counter
  ;; (depending on whether address size is 64 bits, 32 bits, or 16
  ;; bits)."

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08
                                         riml32
                                         rime-size
                                         select-address-size)
                                        ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d* (rime-size)
                                                 (unsigned-byte-p
                                                  member-equal
                                                  acl2::logtail-identity
                                                  not
                                                  rml-size
                                                  select-operand-size)))))
  :prepwork
  ((local (in-theory (e/d* (far-jump-guard-helpers)
                           (unsigned-byte-p
                            member-equal
                            acl2::logtail-identity
                            not)))))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'LOOP #xE0 '(:nil nil)
                                      'x86-loop)
    (add-to-implemented-opcodes-table 'LOOP #xE1 '(:nil nil)
                                      'x86-loop)
    (add-to-implemented-opcodes-table 'LOOP #xE2 '(:nil nil)
                                      'x86-loop))

  :body

  (b* ((ctx 'x86-loop)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ;; temp-rip right now points to the rel8 byte.  Add 1 to
       ;; temp-rip to account for rel8 when computing the length
       ;; of this instruction.
       (badlength? (check-instruction-length start-rip temp-rip 1))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 2 8) counter-size) (select-address-size p4? x86))
       (counter (rgfi-size counter-size *rcx* rex-byte x86))
       (counter (trunc counter-size (1- counter)))

       ((the (unsigned-byte 1) zf) (flgi #.*zf* x86))

       (branch-cond
        (if (equal opcode #xE2) ;; LOOP
            (not (equal counter 0))
          (if (equal opcode #xE1) ;; LOOPE/LOOPZ
              (and (equal zf 1)
                   (not (equal counter 0)))
            ;; #xE0: LOOPNE/LOOPNZ
            (and (equal zf 0)
                 (not (equal counter 0)))))))

    (if branch-cond

        ;; branch condition is true:
        (b* (;; read rel8 (a value between -128 and +127):
             ((mv flg rel8 x86) (rime-size 1 temp-rip *cs* :x nil x86))
             ((when flg) (!!ms-fresh :rime-size-error flg))
             ;; add rel8 to the address of the next instruction,
             ;; which is one past temp-rip to take the rel8 byte into account:
             ((mv flg next-rip) (add-to-*ip temp-rip (1+ rel8) x86))
             ((when flg) (!!ms-fresh :rip-increment-error flg))
             ;; set instruction pointer to new value:
             (x86 (write-*ip next-rip x86)))
          x86)

      ;; branch condition is false:
      (b* (;; go to the next instruction,
           ;; which starts just after the rel8 byte:
           ((mv flg next-rip) (add-to-*ip temp-rip 1 x86))
           ((when flg) (!!ms-fresh :rip-increment-error flg))
           (x86 (write-*ip next-rip x86)))
        x86))))

;; ======================================================================
