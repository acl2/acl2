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

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((byte-operand? (eql opcode #xEB)) ; T if jump short
       ((the (integer 0 4) offset-size)
        (select-operand-size
         proc-mode byte-operand? rex-byte nil prefixes nil t t x86))

       ((mv ?flg (the (signed-byte 32) offset) x86)
        (rime-size proc-mode offset-size temp-rip #.*cs* :x nil x86))
       ((when flg) (!!ms-fresh :rime-size-error flg))

       ((mv flg next-rip)
        (add-to-*ip proc-mode temp-rip (the (integer 0 4) offset-size) x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip next-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg temp-rip) (add-to-*ip proc-mode next-rip offset x86))
       ((when flg) (!!ms-fresh :virtual-memory-error temp-rip))

       ;; when the size is 16 bits, zero the high bits of EIP
       ;; (see pseudocode of JMP in Intel manual, Mar'17, Vol. 2:
       (temp-rip (if (eql offset-size 2)
                     (logand #xffff temp-rip)
                   temp-rip))

       ;; Update the x86 state:
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-near-jmp-Op/En-M

  ;; Absolute indirect jump: RIP = r/m16/32/64
  ;; FF/4: JMP r/m16
  ;; FF/4: JMP r/m32
  ;; FF/4: JMP r/m64
  ;; Op/En: M

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :modr/m t

  :body

  (b* (;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 4 when this
       ;; function is called.

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 2 8) operand-size)
        (select-operand-size proc-mode nil rex-byte nil prefixes t t t x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg
            jmp-addr
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access* operand-size inst-ac?
         nil ;; Not a memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes-error flg))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Note that instruction pointers are modeled as signed in 64-bit mode,
       ;; but unsigned in 32-bit mode.
       (jmp-addr (if (equal proc-mode #.*64-bit-mode*)
                     (i64 jmp-addr)
                   jmp-addr))
       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). See pseudocode in Intel
       ;; manual.
       ((unless (if (equal proc-mode #.*64-bit-mode*)
                    (canonical-address-p jmp-addr)
                  (b* ((cs.limit (the (unsigned-byte 32)
                                   (xr :seg-hidden-limit #.*cs* x86))))
                    (and (<= 0 jmp-addr) (<= jmp-addr cs.limit)))))
        (!!fault-fresh :gp 0 :bad-return-address jmp-addr)) ;; #GP(0)

       ;; Update the x86 state:
       (x86 (write-*ip proc-mode jmp-addr x86)))
      x86))

(local
 (defthm unsigned-byte-p-128-xr-str
   (implies (x86p x86)
            (unsigned-byte-p 128 (xr :str i x86)))))

(local
 (defthmd signed-byte-p-64-when-unsigned-byte-p-48
   (implies (unsigned-byte-p 48 x)
            (signed-byte-p 64 x))))

(local
 (defthmd signed-byte-p-64-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 x)
            (signed-byte-p 64 x))))

(local
 (defthmd signed-byte-p-48-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 x)
            (signed-byte-p 48 x))))

(local
 (defthm unsigned-byte-p-1-bool->bit
   (unsigned-byte-p 1 (bool->bit x))))

(local
 (defthm unsigned-byte-p-3-mv-nth-2-x86-operand-from-modr/m-and-sib-bytes
   (implies
    (x86p x86)
    (unsigned-byte-p
     3
     (mv-nth 2
             (x86-operand-from-modr/m-and-sib-bytes
              proc-mode reg-type
              operand-size inst-ac? memory-ptr?
              seg-reg p4? temp-rip rex-byte
              r/m mod sib num-imm-bytes x86))))))

(local
 (defthm jmp-addr-limit-lemma
   (implies (and (unsigned-byte-p 16 x)
                 (unsigned-byte-p 4 y))
            (signed-byte-p 48
                           (1- (ash (logior x (ash y 16)) 12))))
   :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                     bitops::ihsext-recursive-redefs)
                                    ())))))
(local
 (defthm ret-forcing-round-helper-1
   (implies (x86p x86)
            (unsigned-byte-p
             96
             (xr
              :str #.*gdtr*
              (mv-nth 4
                      (x86-operand-from-modr/m-and-sib-bytes
                       proc-mode reg-type
                       operand-size inst-ac? memory-ptr?
                       seg-reg p4? temp-rip rex-byte
                       r/m mod sib num-imm-bytes x86)))))))

(local
 (defthm ret-forcing-round-helper-2
   (implies (x86p x86)
            (unsigned-byte-p
             96
             (xr
              :str #.*gdtr*
              (mv-nth 2 (rml-size n addr r-x x86)))))))

(local
 (defthm ret-forcing-round-helper-3
   (implies (x86p x86)
            (unsigned-byte-p
             16
             (make-code-segment-attr-field
              (mv-nth 1 (rml-size 8 addr r-x x86)))))))

(local
 (defthm unsigned-byte-p-96-of-xr-str
   (unsigned-byte-p 96 (xr :str i x86))))

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

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d* () (select-operand-size)))))

  :prepwork
  ((local (in-theory (e/d* (far-jump-guard-helpers
                            bigger-bound-of-mv-nth-1-x86-operand-from-modr/m-and-sib-bytes-operand)
                           (unsigned-byte-p
                            member-equal
                            acl2::logtail-identity
                            not
                            signed-byte-p
                            (tau-system))))))

  :guard-hints (("Goal" :in-theory (enable
                                    signed-byte-p-64-when-unsigned-byte-p-48
                                    signed-byte-p-64-when-unsigned-byte-p-32
                                    ;; [Shilpi] TODO Define linear rules for
                                    ;; the following...
                                    call-gate-descriptorbits->offset31-16
                                    call-gate-descriptorbits->offset15-0
                                    gdtr/idtrbits->limit
                                    )))

  :modr/m t

  :body

  (b* (;; Note that this exception was not mentioned in the Intel
       ;; Manuals, but I think that the reason for this omission was
       ;; that the JMP instruction reference sheet mentioned direct
       ;; addressing opcodes too (which are unavailable in the 64-bit
       ;; mode).  If the source operand is not a memory location, then
       ;; #GP(0) is raised.
       ((when (equal mod #b11))
        (!!ms-fresh :source-operand-not-memory-location mod))

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 2 8) offset-size)
        (select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg
            mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte 64) ?addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         proc-mode #.*gpr-access*
         ;; offset-size is the number of bytes of the
         ;; offset.  We need two more bytes for the selector.
         (the (integer 2 10) (+ 2 offset-size)) inst-ac?
         t ;; A memory pointer operand
         seg-reg p4? temp-rip rex-byte r/m mod sib
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
        (segment-selectorBits->index selector))
       ((the (unsigned-byte 1) sel-ti)
        (segment-selectorBits->ti selector))
       ((the (unsigned-byte 2) sel-rpl)
        (segment-selectorBits->rpl selector))

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
            (b* ((gdtr (the (unsigned-byte 80) (stri #.*gdtr* x86)))
                 (gdtr-base (if (eql proc-mode #.*64-bit-mode*)
                                (gdtr/idtrBits->base-addr gdtr)
                              (n32 (gdtr/idtrBits->base-addr gdtr))))
                 (gdtr-limit (gdtr/idtrBits->limit gdtr)))
              (mv gdtr-base gdtr-limit))
          ;; Selector references the LDT whose base address is in
          ;; LDTR.
          (b* ((ldtr-base
                (the (unsigned-byte 64) (ssr-hidden-basei #.*ldtr* x86)))
               (ldtr-base (if (eql proc-mode #.*64-bit-mode*)
                              ldtr-base
                            (n32 ldtr-base)))
               (ldtr-limit
                (the (unsigned-byte 32) (ssr-hidden-limiti #.*ldtr* x86))))
            (mv ldtr-base ldtr-limit))))

       ;; We start by reading 8 bytes from the descriptor table, because code
       ;; segments are always 8 bytes long.

       ;; Is the limit of the selector within the descriptor table limit?
       ;; To obtain the largest address of the descriptor that we are
       ;; reading from the GDT or LDT, we multiply the selector index by 8
       ;; and we add 7 to it, because a code descriptor is 8 bytes long (see
       ;; AMD manual, Dec'17, Volume 2, Figures 4-14 and 4-20).
       (largest-address (+ (ash sel-index 3) 7))
       ((when (< dt-limit largest-address))
        (!!fault-fresh
         :gp sel-index ;; #GP(selector)
         :gp-selector-limit-check-failed (list selector dt-base-addr dt-limit)))

       ;; Now that we know the segment selector is valid, we check if
       ;; the segment descriptor address is valid.
       (descriptor-addr
        ;; The index is scaled by 8.
        (+ dt-base-addr (the (unsigned-byte 16) (ash sel-index 3))))
       ((when (not (canonical-address-p descriptor-addr)))
        (!!ms-fresh :descriptor-addr-virtual-memory-error descriptor-addr))

       ;; Now we read the descriptor (or the first 8 bytes of it if we are in
       ;; 64-bit mode and it is not a code descriptor):
       ((mv flg (the (unsigned-byte 64) descriptor) x86)
        ;; [TO-DO@Shilpi]: I believe I should use :x below and not
        ;; :r. Double check.
        (rml-size 8 descriptor-addr :x x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))

       ;; Now we look at the descriptor just read to see what kind it is,
       ;; and to process it according to the cases in the pseudocode in
       ;; Intel manual, May'18, Volume 2, JMP specification.

       ;; Read the S bit, which is 0 for system segments and 1 for user segments
       ;; (AMD manual, Dec'17, Volume 2, Table 4-2).
       ;; We use CODE-SEGMENT-DESCRIPTOR-LAYOUTBITS->* even though we don't know
       ;; whether this is a code segment yet; it could be a system segment, or
       ;; the first half of it in 64-bit mode. But we need to read the S bit
       ;; somehow, and CODE-SEGMENT-DESCRIPTOR-LAYOUTBITS->* does that.
       ;; TODO: maybe introduce and use a generic function to read the S bit
       ;; from a segment descriptor that is not necessarily a code segment?
       (s (code-segment-descriptorBits->s descriptor))

       ;; If S = 1, the descriptor is for a user segment. The only kind of user
       ;; segment valid for JMP is a code segment. So we process this descriptor
       ;; as a code descriptor segment.
       ((when (= s 1))

        ;; Process conforming or non-conforming code segment:

        ;; The treatment of Conforming and Non-Conforming code segments here
        ;; only differs in the privilege check (see pseudocode in Intel manual,
        ;; May'18, Volume 2, JMP specification). So we use almost the same ACL2
        ;; code (below) for them.

        (b* ( ;; Ensure that the most significant bit of the Type field is 1
             ;; (i.e. code segment), not 0 (i.e. data segment). See AMD manual,
             ;; Dec'17, Volume 2, Table 4-3; the bit is referred to as 'Bit 11'
             ;; there, because it is bit 11 of the high quadword of the
             ;; descriptor (see Figure 4-14).
             (msb-of-type
              (code-segment-descriptorBits->msb-of-type descriptor))
             ((unless (= msb-of-type 1))
              (!!fault-fresh
               :gp sel-index ;; #GP(selector)
               :jmp-far-data-segment sel-index))

             ;; Ensure that D = 0 in 64-bit mode:
             (d (code-segment-descriptorBits->d descriptor))
             ;; This condition is equivalent to Intel pseudocode's condition
             ;; (see 64-BIT-MODEP):
             ((when (and (eql proc-mode #.*64-bit-mode*) (= d 1)))
              (!!fault-fresh
               :gp sel-index ;; #GP(selector)
               :cs.d=1-in-64-bit-mode sel-index))

             ;; Privilege check (differs for conforming and nonconforming
             ;; code segments):
             (cpl (cpl x86))
             (dpl (code-segment-descriptorBits->dpl descriptor))
             (c (code-segment-descriptorBits->c descriptor))
             (allowed (if (= c 1) ; conforming
                          ;; Access is allowed to a conforming code segment
                          ;; when DPL <= CPL (numerically).  RPL is ignored
                          ;; for this privilege check.
                          (<= dpl cpl)
                        ;; Access is allowed to a conforming code segment
                        ;; when RPL <= CPL (numerically) and CPL = DPL.
                        (and (<= sel-rpl cpl)
                             (equal cpl dpl))))
             ;; If access is not allowed, #GP(segment-selector) is raised.
             ((when (not allowed))
              (!!fault-fresh
               :gp sel-index ;; #GP(selector)
               :privilege-check-fail (acons :dpl dpl
                                            (acons :cpl cpl
                                                   (acons :rpl sel-rpl nil)))))

             ;; Ensure that the segment is present:
             (p (code-segment-descriptorBits->p descriptor))
             ((unless (= p 1))
              (!!fault-fresh
               :np sel-index ;; #NP(selector)
               :code-segment-not-present sel-index))

             ;; Trimming the offset based on the operand-size,
             ;; and changing the sign in 64-bit mode:
             (jmp-addr
              (case offset-size
                (2 (n16 offset))
                (4 (n32 offset))
                (t (i64 offset))))

             ;; #GP(0) is thrown if the target offset in destination is
             ;; non-canonical (in 64-bit mode) or outside the segment limit (in
             ;; 32-bit mode):
             (jmp-addr-ok
              (if (eql proc-mode #.*64-bit-mode*)
                  (canonical-address-p jmp-addr)
                (b* ((limit15-0 (code-segment-descriptorBits->limit15-0
                descriptor))
                     (limit19-16 (code-segment-descriptorBits->limit19-16
                                  descriptor))
                     (limit (part-install limit15-0
                                          (ash limit19-16 16)
                                          :low 0 :width 16))
                     (g (code-segment-descriptorBits->g descriptor))
                     ;; If G = 1, the limit is the number of 4-Kbyte blocks
                     ;; (AMD manual, Dec'17, Volume 2, Section 4.7.1):
                     (max-offset
                      (if (= g 1)
                          (1- (ash limit 12))
                        limit)))
                  (< jmp-addr max-offset))))
             ((unless jmp-addr-ok)
              (!!fault-fresh
               :gp 0 ;; #GP(0)
               :noncanonical-or-outside-segment-limit jmp-addr))

             ;; Calculate the new contents of the CS register:
             (new-cs-visible
              (!segment-selectorBits->rpl cpl selector))
             ;; Update x86 state:
             (x86 (!seg-visiblei #.*cs* new-cs-visible x86))
             (x86 (!seg-hidden-basei  #.*cs* dt-base-addr  x86))
             (x86 (!seg-hidden-limiti  #.*cs* dt-limit x86))
             (x86 (!seg-hidden-attri  #.*cs*
                                      ;; Get attributes from the descriptor in GDT.
                                      (make-code-segment-attr-field descriptor)
                                      x86))
             (x86 (write-*ip proc-mode jmp-addr x86)))
          x86))

       ;; Here S = 0, so the descriptor just read is a system segment,
       ;; or the first half of it in 64-bit mode.

       ;; In 32-bit mode, we only support JMP far in the application-level
       ;; view, not in the system-level view of 32-bit mode. Only code
       ;; segments, handled above, are used in the application-level view; call
       ;; gates, handled below, are used in the system-level view. Thus, at
       ;; this point we stop if we are in 32-bit mode. Support for system
       ;; segments in 32-bit mode will be added eventually.

       ((when (not (equal proc-mode #.*64-bit-mode*)))
        (!!ms-fresh :far-jmp-system-unimplemented-in-32-bit-mode))

       ;; Here we know we are in 64-bit mode. Thus, we have just read the first
       ;; 8 bytes of a system descriptor (which is always 16 bytes in 64-bit
       ;; mode). So now we read a 16-byte descriptor from the table, checking
       ;; the limit (TODO: maybe optimize this by just reading the next 8 bytes
       ;; and joining them with the already read 8 bytes above):
       (largest-address (+ (ash sel-index 3) 15))
       ((when (< dt-limit largest-address))
        (!!fault-fresh
         :gp sel-index ;; #GP(selector)
         :gp-selector-limit-check-failed (list selector dt-base-addr dt-limit)))
       ((mv flg (the (unsigned-byte 128) descriptor) x86)
        ;; [TO-DO@Shilpi]: I believe I should use :x below and not
        ;; :r. Double check.
        (rml-size 16 descriptor-addr :x x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))

       ;; Check if the descriptor is a call gate descriptor:
       ((mv call-gate-desc? reason2)
        ;; Note that the following predicate reports the
        ;; descriptor to be invalid if the P flag of the
        ;; descriptor is 0.
        (ia32e-valid-call-gate-segment-descriptor-p descriptor))

       ;; If it is a call gate descriptor, process it accordingly:
       ((when call-gate-desc?)

        (b* ((cpl (cpl x86))
             (dpl (call-gate-descriptorBits->dpl descriptor))

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
              (!!fault-fresh
               :gp sel-index ;; #GP(selector)
               :privilege-check-fail (acons :dpl dpl
                                            (acons :cpl cpl
                                                   (acons :rpl sel-rpl nil)))))

             (cs-selector
              (call-gate-descriptorBits->selector descriptor))
             ((the (unsigned-byte 13) cs-sel-index)
              (segment-selectorBits->index cs-selector))
             ((the (unsigned-byte 1) cs-sel-ti)
              (segment-selectorBits->ti cs-selector))
             ((the (unsigned-byte 2) cs-sel-rpl)
              (segment-selectorBits->rpl cs-selector))

             ;; If the call gate's code segment selector is NULL,
             ;; #GP(0) is raised.
             ((when (and (equal cs-sel-ti 0)
                         (equal cs-sel-index 0)))
              (!!fault-fresh :gp 0 ;; #GP(0)
                             :call-gate-code-segment-nullselector 0))

             ;; Is the call gate code segment selector index outside
             ;; the descriptor table limit?  If so, #GP(code segment
             ;; selector) is raised.
             ((mv cs-dt-base-addr cs-dt-limit)
              (if (equal sel-ti 0)
                  ;; Code Segment Selector references the GDT.
                  (b* ((gdtr (the (unsigned-byte 80) (stri #.*gdtr* x86)))
                       (gdtr-base (gdtr/idtrBits->base-addr gdtr))
                       (gdtr-base (if (eql proc-mode *64-bit-mode*)
                                      gdtr-base
                                    (n32 gdtr-base)))
                       (gdtr-limit (gdtr/idtrBits->limit gdtr)))
                    (mv gdtr-base gdtr-limit))
                ;; Code Segment Selector references the LDT whose base
                ;; address is in LDTR.
                (b* ((ldtr-base (the (unsigned-byte 64)
                                  (ssr-hidden-basei #.*ldtr* x86)))
                     (ldtr-base (if (eql proc-mode #.*64-bit-mode*)
                                    ldtr-base
                                  (n32 ldtr-base)))
                     (ldtr-limit (the (unsigned-byte 32)
                                   (ssr-hidden-limiti #.*ldtr* x86))))
                  (mv ldtr-base ldtr-limit))))
             ;; To obtain the largest address of the descriptor that we are
             ;; reading from the GDT or LDT, we multiply the selector index by 8
             ;; and we add 7 to it, becausea code descriptor is 8 bytes long (see
             ;; AMD manual, Dec'17, Volume 2, Figures 4-14 and 4-20).
             (largest-address (+ (ash cs-sel-index 3) 7))
             ((when (< cs-dt-limit largest-address))
              (!!fault-fresh :gp cs-sel-index
                             :gp-selector-limit-check-failed (list
                                                              cs-selector
                                                              cs-dt-base-addr
                                                              cs-dt-limit)))

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
              (!!fault-fresh
               :gp cs-sel-index ;; #GP(selector)
               :call-gate-code-segment-descriptor-invalid (cons reason cs-descriptor)))

             ;; Checking the privileges of the code segment:
             (cs-dpl (code-segment-descriptorBits->dpl cs-descriptor))
             (c-bit (code-segment-descriptorBits->c cs-descriptor))
             ((when (or (and ;; Conforming code segment
                         (equal c-bit 1)
                         (not (<= cs-dpl cpl)))
                        (and ;; Conforming code segment
                         (equal c-bit 0)
                         (not (eql cs-dpl cpl)))))
              (!!fault-fresh :gp cs-sel-index ;; #GP(selector)
                             :privilege-check-fail (acons :c-bit c-bit
                                                          (acons :cpl cpl
                                                                 (acons :cs-dpl cs-dpl nil)))))

             (call-gate-offset15-0
              (call-gate-descriptorBits->offset15-0 descriptor))
             (call-gate-offset31-16
              (call-gate-descriptorBits->offset31-16 descriptor))
             (call-gate-offset63-32 ;; this is 0 in 32-bit mode
              (call-gate-descriptorBits->offset63-32 descriptor))
             (call-gate-offset31-0
              (mbe :logic (part-install call-gate-offset15-0
                                        (ash call-gate-offset31-16 16)
                                        :low 0 :width 16)
                   :exec
                   (the (unsigned-byte 32)
                     (logior (the (unsigned-byte 16) call-gate-offset15-0)
                             (the (unsigned-byte 32)
                               (ash call-gate-offset31-16 16))))))
             (call-gate-offset
              (mbe :logic
                   (part-install call-gate-offset31-0
                                 (ash call-gate-offset63-32 32)
                                 :low 0 :width 32)
                   :exec
                   (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 32) call-gate-offset31-0)
                             (the (unsigned-byte 64)
                               (ash call-gate-offset63-32 32))))))

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
              (!segment-selectorBits->rpl cpl cs-selector))
             ;; Update x86 state:
             (x86 (!seg-visiblei #.*cs* new-cs-visible x86))
             (x86 (!seg-hidden-basei  #.*cs* cs-dt-base-addr x86))
             (x86 (!seg-hidden-limiti  #.*cs* cs-dt-limit x86))
             (x86 (!seg-hidden-attri #.*cs*
                                     ;; Get attributes from the descriptor in GDT.
                                     (make-code-segment-attr-field cs-descriptor)
                                     x86))
             (x86 (write-*ip proc-mode jmp-addr x86)))
          x86)))

    ;; If it is not a code segment or call gate descriptor, since we are in
    ;; 64-bit mode for now, #GP(selector) is raised.
    (!!fault-fresh
     :gp sel-index ;; #GP(selector)
     :either-both-code-segment-or-call-gate-are-absent-or-some-other-descriptor-is-present
     (cons reason2 descriptor))))

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

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal"
                         :in-theory
                         (e/d* (rime-size)
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

  :body

  (b* (;; temp-rip right now points to the rel8 byte.  Add 1 to
       ;; temp-rip to account for rel8 when computing the length
       ;; of this instruction.
       (badlength? (check-instruction-length start-rip temp-rip 1))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))

       ((the (integer 2 8) counter-size) (select-address-size proc-mode p4? x86))
       (counter (rgfi-size counter-size *rcx* rex-byte x86))
       (counter (trunc counter-size (1- counter)))

       ((the (unsigned-byte 1) zf) (flgi :zf x86))

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
        (b* ( ;; read rel8 (a value between -128 and +127):
             ((mv flg rel8 x86) (rime-size proc-mode 1 temp-rip #.*cs* :x nil x86))
             ((when flg) (!!ms-fresh :rime-size-error flg))
             ;; add rel8 to the address of the next instruction,
             ;; which is one past temp-rip to take the rel8 byte into account:
             ((mv flg next-rip) (add-to-*ip proc-mode temp-rip (1+ rel8) x86))
             ((when flg) (!!ms-fresh :rip-increment-error flg))
             ;; update counter:
             (x86 (!rgfi-size counter-size *rcx* counter rex-byte x86))
             ;; set instruction pointer to new value:
             (x86 (write-*ip proc-mode next-rip x86)))
          x86)

      ;; branch condition is false:
      (b* ( ;; go to the next instruction,
           ;; which starts just after the rel8 byte:
           ((mv flg next-rip) (add-to-*ip proc-mode temp-rip 1 x86))
           ((when flg) (!!ms-fresh :rip-increment-error flg))
           ;; update counter:
           (x86 (!rgfi-size counter-size *rcx* counter rex-byte x86))
           ;; set instruction pointer to new value:
           (x86 (write-*ip proc-mode next-rip x86)))
        x86))))

;; ======================================================================
