;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "../guard-helpers"))

;; ======================================================================
;; INSTRUCTION: SYSCALL
;; ======================================================================

(def-inst x86-syscall-app-view

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  ;; Note: No segment register updates/accesses here since we do not
  ;; support segments at this time.

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (app-view x86)
                               (canonical-address-p temp-rip)))

  ;; Since this function does not specify the actual semantics of the
  ;; SYSCALL instruction, we do not add anything to the
  ;; implemented-opcodes-table, and we prefer to do that for the
  ;; "true" instruction semantic function x86-syscall instead.
  :implemented
  (make-event
   (value (quote
           (value-triple
            (cw "~%~%Nothing added to the implemented-opcodes-table.~%~%~%")))))

  :guard-hints (("Goal" :in-theory (e/d () (msri-is-n64p))
                 :use ((:instance msri-is-n64p (i 0)))))

  :body

  (b* ((ctx 'x86-syscall-app-view)
       ;; 64-bit mode exceptions
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
                              (zp ia32-efer-lma))
                   :exec (or (equal 0 ia32-efer-sce)
                             (equal 0 ia32-efer-lma))))
        (!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))

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

       ((the (unsigned-byte 32) eflags)
        (!rflags-slice :tf 1 eflags))

       (x86 (wr64 *r11* eflags x86)) ;; SYSCALL

       (rax (rr64 *rax* x86))

       ;; See
       ;; http://lxr.free-electrons.com/source/arch/x86/include/asm/syscall.h#L24.
       ;; "Only the low 32 bits of orig_ax are meaningful, so we
       ;; return int.  This importantly ignores the high bits on
       ;; 64-bit, so comparisons
       ;; sign-extend the low 32 bits."

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
       ;; bit 2.

       (x86 (!flgi #.*rf* 0 x86))
       (x86 (!flgi #.*vm* 0 x86)) ;; SYSRET

       ;; SYSCALL loads a new rip from the ia32_lstar (64-bit
       ;; mode). Upon return, SYSRET copies the value saved in rcx to
       ;; the rip. Here, we cheat and directly assign temp-rip to rip.

       (x86 (!rip temp-rip x86))) ;; SYSRET
      x86))

(def-inst x86-syscall

  ;; Fast System Call to privilege level 0 system procedures.
  ;; Op/En: NP
  ;; 0F 05: SYSCALL

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (not (app-view x86))
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SYSCALL #x0F05 '(:nil nil)
                                    'x86-syscall)

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
                                        ())))

  :body

  (b* ((ctx 'x86-syscall)
       ;; 64-bit mode exceptions
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
                              (zp ia32-efer-lma))
                   :exec (or (equal 0 ia32-efer-sce)
                             (equal 0 ia32-efer-lma))))
        (!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))
       (cs-hidden-descriptor (seg-hiddeni *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden-descriptor))
       (cs.l (code-segment-descriptor-attributes-layout-slice :l cs-attr))
       ((when (not (equal cs.l 1)))
        (!!ms-fresh :cs.l!=1 (cons 'cs-hidden-descriptor cs-hidden-descriptor)))

       ;; Update the x86 state:

       ;; SYSCALL saves the rip of the instruction following SYSCALL
       ;; to rcx.
       ;; RCX <- RIP
       (x86 (!rgfi *rcx* temp-rip x86))

       ;; RIP <- IA32_LSTAR
       (lstar (msri *ia32_lstar-idx* x86))
       (lstar-addr (n64-to-i64 lstar))
       ((when (not (canonical-address-p lstar-addr)))
        (!!ms-fresh :lstar-not-canonical lstar))
       (x86 (!rip lstar-addr x86))

       ;; R11 <- RFLAGS
       ;; Shilpi: The AMD manual says that R11 contains the rflags
       ;; value with RF cleared but the Intel manual is silent about
       ;; this.
       ((the (unsigned-byte 32) eflags) (rflags x86))
       (x86 (wr64 *r11* eflags x86))

       ;; RFLAGS <- RFLAGS AND NOT(IA32_FMASK)
       ;; Shilpi: The AMD manual says that RFLAGS.RF is cleared but
       ;; the Intel manual is silent about this.
       (fmask (msri *ia32_fmask-idx* x86))
       (not-fmask (lognot fmask))
       (new-eflags (the (unsigned-byte 32) (logand eflags not-fmask)))
       (x86 (!rflags new-eflags x86))

       ;; CS.Selector <- IA32_STAR[47:32] AND FFFCH
       ;; OS provides CS; RPL forced to 0.
       (star (msri *ia32_star-idx* x86))
       (new-cs-selector
        (the (unsigned-byte 16)
          (logand (part-select star :low 32 :high 47)
                  #xfffc)))
       (x86 (!seg-visiblei *cs* new-cs-selector x86))

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
       (cs-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :base-addr 0
         (!hidden-seg-reg-layout-slice
          :limit #xfffff cs-hidden-descriptor)))

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
        (!code-segment-descriptor-attributes-layout-slice
         :a 1
         (!code-segment-descriptor-attributes-layout-slice
          :r 1
          (!code-segment-descriptor-attributes-layout-slice
           :c 0
           (!code-segment-descriptor-attributes-layout-slice
            :msb-of-type 1
            (!code-segment-descriptor-attributes-layout-slice
             :s 1
             (!code-segment-descriptor-attributes-layout-slice
              :dpl 0
              (!code-segment-descriptor-attributes-layout-slice
               :p 1
               (!code-segment-descriptor-attributes-layout-slice
                :l 1
                (!code-segment-descriptor-attributes-layout-slice
                 :d 0
                 (!code-segment-descriptor-attributes-layout-slice
                  :g 1
                  cs-attr)))))))))))

       (cs-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :attr cs-attr cs-hidden-descriptor))

       (x86 (!seg-hiddeni *cs* cs-hidden-descriptor x86))


       ;; CPL     <- 0;
       (current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (current-cs-register (!seg-sel-layout-slice :rpl 0 current-cs-register))
       (x86 (!seg-visiblei *cs* current-cs-register x86))

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
       (x86 (!seg-visiblei *ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <-  0;      (* Flat segment *)
       ;; SS.Limit <-  FFFFFH; (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-hidden-descriptor (seg-hiddeni *ss* x86))
       (ss-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :base-addr 0
         (!hidden-seg-reg-layout-slice
          :limit #xfffff ss-hidden-descriptor)))
       (ss-attr (hidden-seg-reg-layout-slice :attr ss-hidden-descriptor))

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
        (!data-segment-descriptor-attributes-layout-slice
         :a 1
         (!data-segment-descriptor-attributes-layout-slice
          :w 1
          (!data-segment-descriptor-attributes-layout-slice
           :e 0
           (!data-segment-descriptor-attributes-layout-slice
            :msb-of-type 0
            (!data-segment-descriptor-attributes-layout-slice
             :s 1
             (!data-segment-descriptor-attributes-layout-slice
              :dpl 0
              (!data-segment-descriptor-attributes-layout-slice
               :p 1
               (!data-segment-descriptor-attributes-layout-slice
                :d/b 1
                (!data-segment-descriptor-attributes-layout-slice
                 :g 1
                 ss-attr))))))))))

       (ss-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :attr ss-attr ss-hidden-descriptor))

       (x86 (!seg-hiddeni *ss* ss-hidden-descriptor x86)))

    x86))

;; ======================================================================
;; INSTRUCTION: SYSRET
;; ======================================================================

(def-inst x86-sysret

  :parents (two-byte-opcodes)

  :short "Return from fast system call to user code at privilege level
  3"

  :long "<p>Op/En: NP<br/>
REX.W + 0F 07: SYSRET</p>

<p>SYSRET when REX.W is not set is not supported because 0F 07 \(as
  opposed to REX.W + 0F 07\) returns to compatibility mode, not 64-bit
  mode.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (not (app-view x86))
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SYSRET #x0F07 '(:nil nil)
                                    'x86-sysret)

  :prepwork ((local (in-theory (e/d* (sysret-guard-helpers) ())))

             (local
              (defthm sysret-guard-helper
                (implies (and (signed-byte-p 48 temp-rip)
                              (signed-byte-p 48 start-rip))
                         (signed-byte-p 49 (+ (- start-rip) temp-rip))))))

  :guard-hints (("Goal" :in-theory (e/d (n64-to-i64 wr64)
                                        (unsigned-byte-p
                                         signed-byte-p))))

  :body

  (b* ((ctx 'x86-sysret)

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((when (not (logbitp #.*w* rex-byte)))
        (!!ms-fresh :unsupported-sysret-because-rex.w!=1 rex-byte))

       ;; 64-bit mode exceptions

       ;; If the LOCK prefix is used...
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       ;; If SCE or LMA = 0...
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       ((the (unsigned-byte 1) ia32-efer-sce) (ia32_efer-slice :ia32_efer-sce ia32-efer))
       ((the (unsigned-byte 1) ia32-efer-lma) (ia32_efer-slice :ia32_efer-lma ia32-efer))
       ((when (mbe :logic (or (zp ia32-efer-sce)
                              (zp ia32-efer-lma))
                   :exec (or (equal 0 ia32-efer-sce)
                             (equal 0 ia32-efer-lma))))
        (!!ms-fresh :ia32-efer-sce-or-lma=0 (cons 'ia32_efer ia32-efer)))

       ;; If CPL != 0...
       (current-cs-register (the (unsigned-byte 16) (seg-visiblei *cs* x86)))
       (cpl (seg-sel-layout-slice :rpl current-cs-register))
       ((when (not (equal 0 cpl)))
        (!!ms-fresh :cpl!=0 (cons 'cs-register current-cs-register)))

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
        (mbe :logic (logior new-cs-selector 3)
             :exec (!seg-sel-layout-slice :rpl 3 new-cs-selector)))
       (x86 (!seg-visiblei *cs* new-cs-selector x86))

       ;; (* Set rest of CS to a fixed value *)
       ;; CS.Base  <-  0;      (* Flat segment *)
       ;; CS.Limit <- FFFFFH;  (* With 4-KByte granularity, implies a 4-GByte limit *)
       (cs-hidden-descriptor (seg-hiddeni *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden-descriptor))
       (cs-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :base-addr 0
         (!hidden-seg-reg-layout-slice
          :limit #xfffff cs-hidden-descriptor)))

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
        (!code-segment-descriptor-attributes-layout-slice
         :a 1
         (!code-segment-descriptor-attributes-layout-slice
          :r 1
          (!code-segment-descriptor-attributes-layout-slice
           :c 0
           (!code-segment-descriptor-attributes-layout-slice
            :msb-of-type 1
            (!code-segment-descriptor-attributes-layout-slice
             :s 1
             (!code-segment-descriptor-attributes-layout-slice
              :dpl 3
              (!code-segment-descriptor-attributes-layout-slice
               :p 1
               (!code-segment-descriptor-attributes-layout-slice
                :l 1
                (!code-segment-descriptor-attributes-layout-slice
                 :d 0
                 (!code-segment-descriptor-attributes-layout-slice
                  :g 1
                  cs-attr)))))))))))

       (cs-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :attr cs-attr cs-hidden-descriptor))

       (x86 (!seg-hiddeni *cs* cs-hidden-descriptor x86))

       ;; CPL <- 0;
       (current-cs-register (!seg-sel-layout-slice :rpl 0 current-cs-register))
       (x86 (!seg-visiblei *cs* current-cs-register x86))

       ;; SS.Selector <- (IA32_STAR[63:48] + 8) OR 3; (* RPL forced to 3 *)
       (new-ss-selector
        (+ (part-select star :low 48 :high 63) 8))
       ;; Shilpi: How do we know that new-ss-selector fits in 16
       ;; bytes?
       ((when (not (n16p new-ss-selector)))
        (!!ms-fresh :new-ss-selector-too-large new-ss-selector))
       (new-ss-selector
        (mbe :logic (logior new-ss-selector 3)
             :exec (!seg-sel-layout-slice :rpl 3 new-ss-selector)))
       (x86 (!seg-visiblei *ss* new-ss-selector x86))

       ;; (* Set rest of SS to a fixed value *)
       ;; SS.Base  <- 0;           (* Flat segment *)
       ;; SS.Limit <- FFFFFH;      (* With 4-KByte granularity, implies a 4-GByte limit *)
       (ss-hidden-descriptor (seg-hiddeni *ss* x86))
       (ss-attr (hidden-seg-reg-layout-slice :attr ss-hidden-descriptor))
       (ss-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :base-addr 0
         (!hidden-seg-reg-layout-slice
          :limit #xfffff ss-hidden-descriptor)))

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
        (!data-segment-descriptor-attributes-layout-slice
         :a 1
         (!data-segment-descriptor-attributes-layout-slice
          :w 1
          (!data-segment-descriptor-attributes-layout-slice
           :e 0
           (!data-segment-descriptor-attributes-layout-slice
            :msb-of-type 0
            (!data-segment-descriptor-attributes-layout-slice
             :s 1
             (!data-segment-descriptor-attributes-layout-slice
              :dpl 3
              (!data-segment-descriptor-attributes-layout-slice
               :p 1
               (!data-segment-descriptor-attributes-layout-slice
                :d/b 1
                (!data-segment-descriptor-attributes-layout-slice
                 :g 1
                 ss-attr))))))))))

       (ss-hidden-descriptor
        (!hidden-seg-reg-layout-slice
         :attr ss-attr ss-hidden-descriptor))

       (x86 (!seg-hiddeni *ss* ss-hidden-descriptor x86)))

    x86))

;; ======================================================================
