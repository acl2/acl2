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

;; ======================================================================
;; INSTRUCTION: SYSCALL
;; ======================================================================

; The Intel manual only allows SYSCALL and SYSRET in 64-bit mode, while the AMD
; manuals also allow them in 32-bit compatiblity mode. Since the model aims at
; maximizing compatibility with the Intel manual, the following semantic
; functions throw #UD if the processor is not in 64-bit mode.

(def-inst x86-syscall-app-view

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  ;; Note: No segment register updates/accesses here since we do not
  ;; support segment descriptors in the application-level view.

  ;; This semantic function is really a combination of SYSCALL, followed by a
  ;; model of the invoked system call, followed by SYSRET. So it starts as
  ;; SYSCALL, but the final state is the one after the SYSRET, with the model
  ;; of the system call also fully executed. It models a system call in the
  ;; application-level view, where a system call is essentially an "atomic"
  ;; action, since application-level code has no access to the system call
  ;; internals.

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86) (app-view x86)))

  :guard-hints (("Goal" :in-theory (e/d (rflagsbits-p
                                         !rflagsbits->tf)
                                        (unsigned-byte-p))))

  :body

  (b* ((ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce)
        (ia32_eferBits->sce ia32-efer))
       ((when (mbe :logic (zp ia32-efer-sce)
                   :exec (equal 0 ia32-efer-sce)))
        (!!fault-fresh :ud nil ;; #UD
                       :ia32-efer-sce=0 (cons 'ia32_efer ia32-efer)))

       ;; Update the x86 state:

       ;; SYSCALL saves the rip of the instruction following SYSCALL
       ;; to rcx.
       (x86 (!rgfi *rcx* temp-rip x86)) ;; SYSCALL

       ;; rcx is supposed to be destroyed by the kernel for security
       ;; reasons and sometimes, I see -1 in rcx after a syscall
       ;; instruction.

       ;; (x86 (!rgfi *rcx* -1 x86))

       ;; SYSCALL saves RFLAGS into R11 and then masks it using the
       ;; IA32_FMASK MSR. However, SYSRET loads the flags from R11
       ;; after masking it such that RF and VM are cleared and bit 2
       ;; is set. So, I'm just changing the flags accordingly at the
       ;; end of this semantic function.

       ((the (unsigned-byte 32) eflags) (rflags x86))

       ;; IMPORTANT NOTE:
       ;; r11 is also destroyed by the kernel, but all I've seen so
       ;; far is that the value for flags stored in r11 has the trap
       ;; flag set (bit 8, zero-based indexing). However, when flags
       ;; are restored from r11 by the sysret, the trap flag is not
       ;; set.

       ;; Also note that the Jan'13 Intel Manual says (Sec. 3.4.3.3,
       ;; V-1): "They (system flags, of which TF is one) should not be
       ;; modified by application programs."

       (x86 (wr64 *r11* (!rflagsBits->tf 1 eflags) x86)) ;; SYSCALL

       ;; On Linux and macOS, EAX is used to identify the system call to make.
       ;; See
       ;; http://lxr.free-electrons.com/source/arch/x86/include/asm/syscall.h#L24.
       ;; "Only the low 32 bits of orig_ax are meaningful, so we
       ;; return int.  This importantly ignores the high bits on
       ;; 64-bit, so comparisons
       ;; sign-extend the low 32 bits."
       ;; Also see ../syscalls.lisp and syscall-numbers.lisp.
       ;; The model of system calls is discussed in the FMCAD paper.

       (rax (rr64 *rax* x86))
       ((the (unsigned-byte 32) eax) (n32 rax))

       (x86
        (cond
         ((equal eax (sys_read-idx x86)) ;; Read
          (x86-syscall-read x86))
         ((equal eax (sys_write-idx x86)) ;; Write
          (x86-syscall-write x86))
         ((equal eax (sys_open-idx x86)) ;; Open
          (x86-syscall-open x86))
         ((equal eax (sys_close-idx x86)) ;; Close
          (x86-syscall-close x86))
         ((equal eax (sys_stat-idx x86)) ;; Stat
          (x86-syscall-stat x86))
         ((equal eax (sys_lstat-idx x86)) ;; Lstat
          (x86-syscall-lstat x86))
         ((equal eax (sys_fstat-idx x86)) ;; Fstat
          (x86-syscall-fstat x86))
         ((equal eax (sys_lseek-idx x86)) ;; Lseek
          (x86-syscall-lseek x86))
         ((equal eax (sys_dup-idx x86)) ;; Dup
          (x86-syscall-dup x86))
         ((equal eax (sys_dup2-idx x86)) ;; Dup2
          (x86-syscall-dup2 x86))
         ((equal eax (sys_fcntl-idx x86)) ;; Fcntl
          (x86-syscall-fcntl x86))
         ((equal eax (sys_truncate-idx x86)) ;; Truncate
          (x86-syscall-truncate x86))
         ((equal eax (sys_ftruncate-idx x86)) ;; Ftruncate
          (x86-syscall-ftruncate x86))
         ((equal eax (sys_link-idx x86)) ;; Link
          (x86-syscall-link x86))
         ((equal eax (sys_unlink-idx x86)) ;; Unlink
          (x86-syscall-unlink x86))
         ((equal eax (sys_fadvise64-idx x86)) ;; Fadvise64
          (x86-syscall-fadvise64 x86))
         ((equal eax (sys_dup3-idx x86)) ;; Dup3
          (x86-syscall-dup3 x86))
         (t
          (let* ((x86
                  (!ms (list "Unimplemented syscall"
                             'RAX rax
                             'RIP (rip x86))
                       x86)))
            x86))))

       ;; (- (cw "~%~%X86-SYSCALL: If SYSCALL does not return the result you ~
       ;;         expected, then you might want to check whether these ~
       ;;         books were compiled using X86ISA_EXEC set to t. See ~
       ;;         :doc x86isa-build-instructions.~%~%"))


       ((when (ms x86))
        (!!ms-fresh :x86-syscall (ms x86)))

       ;; Clear RF, VM. Reserved bits retain their fixed values. Set
       ;; bit 2 (PF).

       (eflags (!rflagsBits->rf 0 eflags))
       (eflags (!rflagsBits->vm 0 eflags)) ;; SYSRET
       (eflags (!rflagsBits->pf 1 eflags))
       (x86 (!rflags eflags x86))

       ;; SYSCALL loads a new rip from the ia32_lstar (64-bit
       ;; mode). Upon return, SYSRET copies the value saved in rcx to
       ;; the rip. Here, we cheat and directly assign temp-rip to rip.

       (x86 (!rip temp-rip x86))) ;; SYSRET
    x86))

(local
 (defthm-unsigned-byte-p n32p-xr-rflags
   :hyp t
   :bound 32
   :concl (xr :rflags i x86)
   :gen-linear t
   :gen-type t))

(local (include-book "centaur/bitops/width-find-rule" :dir :system))
(local (in-theory (e/d (bitops::unsigned-byte-p-by-find-rule) ())))

(def-inst x86-syscall

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (not (app-view x86))))

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
                                        (unsigned-byte-p))))

  :body

  (b* ((ia32-efer (n12 (msri #.*ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce)
        (ia32_eferBits->sce ia32-efer))
       ((when (mbe :logic (zp ia32-efer-sce)
                   :exec (equal 0 ia32-efer-sce)))
        (!!fault-fresh :ud nil ;; #UD
                       :ia32-efer-sce=0 (cons 'ia32_efer ia32-efer)))

       ((the (unsigned-byte 16) cs-attr) (seg-hidden-attri #.*cs* x86))

       ;; Update the x86 state:

       ;; SYSCALL saves the rip of the instruction following SYSCALL
       ;; to rcx.
       ;; RCX <- RIP
       (x86 (!rgfi #.*rcx* temp-rip x86))

       ;; RIP <- IA32_LSTAR
       (lstar (msri #.*ia32_lstar-idx* x86))
       (lstar-addr (n64-to-i64 lstar))
       ((when (not (canonical-address-p lstar-addr)))
        (!!ms-fresh :lstar-not-canonical lstar))
       (x86 (!rip lstar-addr x86))

       ;; R11 <- RFLAGS
       ;; Shilpi: The AMD manual says that R11 contains the rflags
       ;; value with RF cleared but the Intel manual is silent about
       ;; this.
       ((the (unsigned-byte 32) eflags) (rflags x86))
       (x86 (wr64 #.*r11* eflags x86))

       ;; RFLAGS <- RFLAGS AND NOT(IA32_FMASK)
       ;; Shilpi: The AMD manual says that RFLAGS.RF is cleared but
       ;; the Intel manual is silent about this.
       (fmask (msri #.*ia32_fmask-idx* x86))
       (not-fmask (lognot fmask))
       (new-eflags (the (unsigned-byte 32) (logand eflags not-fmask)))
       (x86 (!rflags new-eflags x86))

       ;; CS.Selector <- IA32_STAR[47:32] AND FFFCH
       ;; OS provides CS; RPL forced to 0.
       (star (msri #.*ia32_star-idx* x86))
       (new-cs-selector
        (the (unsigned-byte 16)
          (logand (part-select star :low 32 :high 47)
                  #xfffc)))
       (x86 (!seg-visiblei #.*cs* new-cs-selector x86))

       ;; From the Intel Vol. 2, Instruction Reference SYSCALL:

       ;;    SYSCALL loads the CS and SS selectors with values derived
       ;;    from bits 47:32 of the IA32_STAR MSR. However, the CS and
       ;;    SS descriptor caches are not loaded from the descriptors
       ;;    (in GDT or LDT) referenced by those selectors. Instead,
       ;;    the descriptor caches are loaded with fixed values. See
       ;;    the Operation section for details. It is the
       ;;    responsibility of OS software to ensure that the
       ;;    descriptors (in GDT or LDT) referenced by those selector
       ;;    values correspond to the fixed values loaded into the
       ;;    descriptor caches; the SYSCALL instruction does not
       ;;    ensure this correspondence.

       ;; (* Set rest of CS to a fixed value *)

       ;; CS.Base   <- 0;       (* Flat segment *)
       ;; CS.Limit  <- FFFFFH;  (* With 4-KByte granularity, implies a 4-GByte limit *)
       (cs-hidden-base-addr 0)
       (cs-hidden-limit #xffffffff) ; this is 32 bits, not 20 bits
       ;; CS.A       <- 1;   (* Accessed. *)
       ;; CS.R       <- 1;   (* Execute/read code. *)
       ;; CS.C       <- 0;
       ;; CS.TypeMSB <- 1;
       ;; CS.S       <- 1;
       ;; CS.DPL     <- 0;
       ;; CS.P       <- 1;
       ;; CS.L       <- 1;   (* Entry is to 64-bit mode *)
       ;; CS.D       <- 0;   (* Required if CS.L = 1 *)
       ;; CS.G       <- 1;   (* 4-KByte granularity *)
       (cs-attr
        (change-code-segment-descriptor-attributesBits
         cs-attr
         :a 1
         :r 1
         :c 0
         :msb-of-type 1
         :s 1
         :dpl 0
         :p 1
         :l 1
         :d 0
         :g 1))

       (x86 (!seg-hidden-basei #.*cs* cs-hidden-base-addr x86))
       (x86 (!seg-hidden-limiti #.*cs* cs-hidden-limit x86))
       (x86 (!seg-hidden-attri #.*cs* cs-attr x86))

       ;; SS.Selector <- IA32_STAR[47:32] + 8; (* SS just above CS *)
       (new-ss-selector
        (+ (part-select star :low 32 :high 47) 8))
       ;; Shilpi: How do we know that new-ss-selector fits in 16
       ;; bytes? Neither the Intel nor the AMD manuals say anything
       ;; about truncating this value to fit in 16 bits.  So, I'm
       ;; going to raise an error when it doesn't, just so we're aware
       ;; that a "bad" situation happened.
       ((when (not (n16p new-ss-selector)))
        (!!ms-fresh :new-ss-selector-too-large new-ss-selector))
       (x86 (!seg-visiblei #.*ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <-  0;      (* Flat segment *)
       ;; SS.Limit <-  FFFFFH; (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-hidden-base-addr 0)
       (ss-hidden-limit #xffffffff) ; this is 32 bits, not 20 bits
       ((the (unsigned-byte 16) ss-attr) (seg-hidden-attri #.*ss* x86))
       ;; SS.A       <-  1;      (* Accessed. *)
       ;; SS.W       <-  1;      (* Read/write data. *)
       ;; SS.E       <-  0;
       ;; SS.TypeMSB <-  0;
       ;; SS.S       <-  1;
       ;; SS.DPL     <-  0;
       ;; SS.P       <-  1;
       ;; SS.B       <-  1;      (* 32-bit stack segment *)
       ;; SS.G       <-  1;      (* 4-KByte granularity *)
       (ss-attr
        (change-data-segment-descriptor-attributesBits
         ss-attr
         :a 1
         :w 1
         :e 0
         :msb-of-type 0
         :s 1
         :dpl 0
         :p 1
         :d/b 1
         :g 1))

       (x86 (!seg-hidden-basei #.*ss* ss-hidden-base-addr x86))
       (x86 (!seg-hidden-limiti #.*ss* ss-hidden-limit x86))
       (x86 (!seg-hidden-attri #.*ss* ss-attr x86)))

    x86))


(def-inst x86-syscall-both-views

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (if (app-view x86)
      (x86-syscall-app-view
       proc-mode start-rip temp-rip prefixes rex-byte
       opcode modr/m sib x86)
    (x86-syscall
     proc-mode start-rip temp-rip prefixes rex-byte
     opcode modr/m sib x86)))

;; ======================================================================
;; INSTRUCTION: SYSRET
;; ======================================================================

(def-inst x86-sysret

  :parents (two-byte-opcodes)

  :short "Return from fast system call to user code at privilege level
  3"

  :long "<p>Op/En: NP<br/>
 0F 07: SYSRET<br/>
 REX.W + 0F 07: SYSRET</p>

 <p>SYSRET when REX.W is not set is not supported yet because 0F 07
  \(as opposed to REX.W + 0F 07\) switches the machine to
  compatibility mode, not 64-bit mode.</p>"

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork ((local
              (defthm sysret-guard-helper
                (implies (and (signed-byte-p 48 temp-rip)
                              (signed-byte-p 48 start-rip))
                         (signed-byte-p 49 (+ (- start-rip) temp-rip))))))

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
                                        (unsigned-byte-p
                                         signed-byte-p))))

  :body

  (b* ( ;; We can't *call* SYSRET in any mode other than 64-bit mode
       ;; (including compatibility mode), but when it is called from
       ;; the 64-bit mode *without* REX.W, a mode switch to
       ;; compatibility mode is effected.  From then on, the machine
       ;; is in compatibility mode until further mode changes.

       ;; For now, we do require the presence of REX.W with SYSRET.
       ;; SYSRET without REX.W is not supported.

       ;; Source: The pseudocode under SYSRET (Intel Vol. 2, May 2018
       ;; edition) says the following:

       ;; ...
       ;; IF (operand size is 64-bit) THEN
       ;;  (* Return to 64-Bit Mode *)
       ;;  CS.L <- 1; (* 64-bit code segment *)
       ;;  CS.D <- 0; (* Required if CS.L = 1 *)
       ;; ELSE
       ;;  (* Return to Compatibility Mode *)
       ;;  CS.L <- 0; (* Compatibility mode *)
       ;;  CS.D <- 1; (* 32-bit code segment *)
       ;; FI;
       ;; ...
       ((when (not (logbitp #.*w* rex-byte)))
        (!!ms-fresh :unsupported-sysret-because-rex.w!=1 rex-byte))

       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce)
        (ia32_eferBits->sce ia32-efer))
       ((when (mbe :logic (zp ia32-efer-sce)
                   :exec (equal 0 ia32-efer-sce)))
        (!!fault-fresh :ud nil ;; #UD
                       :ia32-efer-sce=0 (cons 'ia32_efer ia32-efer)))

       ;; If CPL != 0...
       (current-cs-register (the (unsigned-byte 16) (seg-visiblei #.*cs* x86)))
       (cpl (segment-selectorBits->rpl current-cs-register))
       ((when (not (equal 0 cpl)))
        (!!fault-fresh :gp 0 ;; #GP(0)
                       :cpl!=0 (cons 'cs-register current-cs-register)))

       ;; If RCX contains a non-canonical address...
       (rcx (rgfi *rcx* x86))
       ((when (not (canonical-address-p rcx)))
        (!!ms-fresh :rcx-non-canonical rcx))

       ;; Update the x86 state:

       ;; Return to 64-bit mode
       (x86 (!rip rcx x86))

       ;; (* Clear RF, VM, reserved bits; set bit 2 *)
       ;; RFLAGS   (R11 & 3C7FD7H) | 2;
       (r11 (n32 (rgfi *r11* x86)))
       (x86 (!rflags (logior (logand r11 #x3c7fd7) 2) x86))

       ;; CS.Selector   IA32_STAR[63:48]+16;
       (star (msri *ia32_star-idx* x86))
       (new-cs-selector
        (+ (part-select star :low 48 :high 63)
           16))
       ;; Shilpi: How do we know that new-cs-selector fits in 16
       ;; bytes?
       ((when (not (n16p new-cs-selector)))
        (!!ms-fresh :new-cs-selector-too-large new-cs-selector))
       ;; CS.Selector   CS.Selector OR 3;  (* RPL forced to 3 *)
       (new-cs-selector
        (!segment-selectorBits->rpl 3 new-cs-selector))
       (x86 (!seg-visiblei #.*cs* new-cs-selector x86))

       ;; (* Set rest of CS to a fixed value *)
       ;; CS.Base  <-  0;      (* Flat segment *)
       ;; CS.Limit <- FFFFFH;  (* With 4-KByte granularity, implies a 4-GByte limit *)
       (cs-base-addr 0)
       (cs-limit #xffffffff) ; this is 32 bits, not 20 bits
       ((the (unsigned-byte 16) cs-attr) (seg-hidden-attri #.*cs* x86))
       ;; CS.A       <- 1;   (* Accessed. *)
       ;; CS.R       <- 1;   (* Execute/read code. *)
       ;; CS.C       <- 0;
       ;; CS.TypeMSB <- 1;
       ;; CS.S       <- 1;
       ;; CS.DPL     <- 3;
       ;; CS.P       <- 1;
       ;; (* Return to 64-Bit Mode *)
       ;; CS.L       <- 1;           (* 64-bit code segment *)
       ;; CS.D       <- 0;           (* Required if CS.L = 1 *)
       ;; CS.G       <- 1;           (* 4-KByte granularity *)
       (cs-attr
        (change-code-segment-descriptor-attributesBits
         cs-attr
         :a 1
         :r 1
         :c 0
         :msb-of-type 1
         :s 1
         :dpl 3
         :p 1
         :l 1
         :d 0
         :g 1))

       (x86 (!seg-hidden-basei #.*cs* cs-base-addr x86))
       (x86 (!seg-hidden-limiti #.*cs* cs-limit x86))
       (x86 (!seg-hidden-attri #.*cs* cs-attr x86))

       ;; CPL <- 0;
       (current-cs-register (!segment-selectorBits->rpl 0 current-cs-register))
       (x86 (!seg-visiblei #.*cs* current-cs-register x86))

       ;; SS.Selector <- (IA32_STAR[63:48] + 8) OR 3; (* RPL forced to 3 *)
       (new-ss-selector
        (+ (part-select star :low 48 :high 63) 8))
       ;; Shilpi: How do we know that new-ss-selector fits in 16
       ;; bytes?
       ((when (not (n16p new-ss-selector)))
        (!!ms-fresh :new-ss-selector-too-large new-ss-selector))
       (new-ss-selector
        (!segment-selectorBits->rpl 3 new-ss-selector))
       (x86 (!seg-visiblei #.*ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <- 0;           (* Flat segment *)
       ;; SS.Limit <- FFFFFH;      (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-base-addr 0)
       (ss-limit #xffffffff) ; this is 32 bits, not 20 bits
       ((the (unsigned-byte 16) ss-attr) (seg-hidden-attri #.*ss* x86))
       ;; SS.A       <-  1;      (* Accessed. *)
       ;; SS.W       <-  1;      (* Read/write data. *)
       ;; SS.E       <-  0;
       ;; SS.TypeMSB <-  0;
       ;; SS.S       <- 1;
       ;; SS.DPL     <- 3;
       ;; SS.P       <- 1;
       ;; SS.B       <- 1;           (* 32-bit stack segment*)
       ;; SS.G       <- 1;           (* 4-KByte granularity *)
       (ss-attr
        (change-data-segment-descriptor-attributesBits
         ss-attr
         :a 1
         :w 1
         :e 0
         :msb-of-type 0
         :s 1
         :dpl 3
         :p 1
         :d/b 1
         :g 1))

       (x86 (!seg-hidden-basei #.*ss* ss-base-addr x86))
       (x86 (!seg-hidden-limiti #.*ss* ss-limit x86))
       (x86 (!seg-hidden-attri #.*ss* ss-attr x86)))

    x86))

;; ======================================================================
