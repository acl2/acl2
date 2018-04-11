;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: CALL
;; ======================================================================

;; From Intel manual, Mar'17, Volume 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

(def-inst x86-call-E8-Op/En-M

  ;; Call near, displacement relative to the next instruction
  ;; Op/En: M
  ;; E8 cd (CALL rel32)
  ;; Note E8 cw (CALL rel16) is N.S. in 64-bit mode.

  ;; The address-size override prefix will not have any effect here
  ;; since we have no memory operands.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xE8 '(:nil nil) 'x86-call-E8-Op/En-M)

  :body

  (b* ((ctx 'x86-call-E8-Op/En-M)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))

       ;; AC is not done during code fetches. Fetching rel32 from the
       ;; instruction stream still qualifies as a code fetch
       ;; (double-check).
       ((mv flg0 (the (signed-byte 32) rel32) x86)
        (riml32 temp-rip :x x86))
       ((when flg0)
        (!!ms-fresh :riml32-error flg0))
       ((the (signed-byte #.*max-linear-address-size+1*) next-rip)
        (+ 4 temp-rip))
       ((when (mbe :logic (not (canonical-address-p next-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               next-rip))))
        (!!ms-fresh :next-rip-invalid next-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           next-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ((the (signed-byte #.*max-linear-address-size+1*) call-rip)
        (+ next-rip rel32))
       ((when (mbe :logic (not (canonical-address-p call-rip))
                   :exec (or
                          (< (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               call-rip) #.*-2^47*)
                          (<= #.*2^47*
                              (the (signed-byte
                                    #.*max-linear-address-size+1*)
                                call-rip)))))
        (!!ms-fresh :temp-rip-invalid call-rip))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp 8))
       ((when (not (canonical-address-p new-rsp)))
        (!!ms-fresh :invalid-new-rsp new-rsp))
       ;; Update the x86 state:
       ;; Push the return address on the stack.
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when
            ;; Check alignment.
            (and
             inst-ac?
             (not (equal (logand new-rsp 7) 0))))
        (!!ms-fresh :memory-access-unaligned new-rsp)) ;; #AC
       ((mv flg1 x86)
        (write-canonical-address-to-memory
         (the (signed-byte #.*max-linear-address-size*) new-rsp)
         next-rip  x86))
       ((when flg1)
        ;; #SS/#GP exception?
        (!!ms-fresh :write-canonical-address-to-memory flg1))
       ;; Update the rip to point to the called procedure.
       (x86 (!rip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (!rgfi *rsp* new-rsp x86)))
      x86))

(def-inst x86-call-FF/2-Op/En-M

  ;; Call near, absolute indirect, address given in r/64.
  ;; Op/En: M
  ;; FF/2 r/m64
  ;; Note that FF/2 r/m16 and r/m32 are N.E. in 64-bit mode.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'CALL #xFF '(:reg 2)
                                    'x86-call-FF/2-Op/En-M)

  :body

  (b* ((ctx ' x86-call-FF/2-Op/En-M)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override* (prefixes-slice :group-4-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       ;; Note that the reg field serves as an opcode extension for
       ;; this instruction.  The reg field will always be 2 when this
       ;; function is called.
       (inst-ac? (alignment-checking-enabled-p x86))
       ((mv flg0 (the (unsigned-byte 64) call-rip) (the (unsigned-byte 3) increment-rip-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* 8 inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))
       ((the (signed-byte #.*max-linear-address-size+1*) next-rip)
        (+ temp-rip increment-rip-by))
       ((when (mbe :logic (not (canonical-address-p next-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               next-rip))))
        (!!ms-fresh :temp-rip-invalid next-rip))
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           next-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Converting call-rip into a "good" address in our world...
       (call-rip (n64-to-i64 call-rip))
       ((when (not (canonical-address-p call-rip)))
        (!!ms-fresh :temp-rip-invalid call-rip))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp 8))
       ((when (not (canonical-address-p new-rsp)))
        (!!ms-fresh :invalid-new-rsp new-rsp))
       ;; Update the x86 state:
       ;; Push the return address on the stack.
       ((when
            ;; Check alignment.
            (and
             inst-ac?
             (not (equal (logand new-rsp 7) 0))))
        (!!ms-fresh :memory-access-unaligned new-rsp))
       ((mv flg1 x86)
        (write-canonical-address-to-memory
         (the (signed-byte #.*max-linear-address-size*) new-rsp)
         (the (signed-byte #.*max-linear-address-size*) next-rip)
         x86))
       ((when flg1)
        (!!ms-fresh :write-canonical-address-to-memory flg1))
       ;; Update the rip to point to the called procedure.
       (x86 (!rip call-rip x86))
       ;; Decrement the stack pointer.
       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: RET
;; ======================================================================

;; From Intel manual, Mar'17, Volume 1, Section 6.3.7:

;; In 64-bit mode, the operand size for all near branches (CALL, RET,
;; JCC, JCXZ, JMP, and LOOP) is forced to 64 bits. These instructions
;; update the 64-bit RIP without the need for a REX operand-size
;; prefix.

;; The following aspects of near branches are controlled by the
;; effective operand size:
;;   Truncation of the size of the instruction pointer
;;   Size of a stack pop or push, due to a CALL or RET
;;   Size of a stack-pointer increment or decrement, due to a CALL or RET
;;   Indirect-branch operand size

;; In 64-bit mode, all of the above actions are forced to 64 bits
;; regardless of operand size prefixes (operand size prefixes are
;; silently ignored). However, the displacement field for relative
;; branches is still limited to 32 bits and the address size for near
;; branches is not forced in 64-bit mode.

;; Address sizes affect the size of RCX used for JCXZ and LOOP; they
;; also impact the address calculation for memory indirect
;; branches. Such addresses are 64 bits by default; but they can be
;; overridden to 32 bits by an address size prefix.

;; In 32-bit mode, the operand size should be the size of the code address,
;; i.e. 32 bits if CS.D = 1 and 16 bits if CS.D = 0. Note that also in 64-bit
;; mode (see above) the operand size (64 bits) is equal to the size of the code
;; address (64 bits, even though in our model we only model the low 48 bits due
;; to the invariant of instruction pointers being canonical).

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-ret

  ;; Op/En: #xC2 iw: I:  Near return to calling procedure and pop imm16 bytes from
  ;;                     stack
  ;;        #xC3:    NP: Near return to calling procedure

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (rime-size rml16 rme-size rme16) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'RET #xC2 '(:nil nil) 'x86-ret)
    (add-to-implemented-opcodes-table 'RET #xC3 '(:nil nil) 'x86-ret))

  :body

  (b* ((ctx 'x86-ret)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!ms-fresh :lock-prefix prefixes))

       (rsp (read-*sp x86))

       ((the (integer 2 8) operand-size)
        (if (64-bit-modep x86)
            8
          (b* ((cs-hidden (xr :seg-hidden *cs* x86))
               (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
               (cs.d
                (code-segment-descriptor-attributes-layout-slice :d cs-attr)))
            (if (= cs.d 1) 4 2))))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) new-rsp) x86)
        (if (equal opcode #xC3)
            (b* (((mv flg1 new-rsp)
                  (add-to-*sp rsp operand-size x86))
                 ((when flg1) (mv flg1 0 x86)))
              (mv nil new-rsp x86))
          ;; We don't do any alignment check below when fetching the
          ;; immediate operand; reading the immediate operand is done
          ;; during code fetching, where alignment checks aren't supposed
          ;; to be done (see Intel Manuals, Volume 3, Section 6.15,
          ;; Exception and Interrupt Reference, Interrupt 17 Alignment
          ;; Check Exception (#AC) for details).
          (b* (((mv flg1 (the (unsigned-byte 16) imm16) x86)
                (rme16 temp-rip *cs* :x nil x86))
               ((when flg1) (mv flg1 0 x86))
               ((mv flg1 new-rsp)
                (add-to-*sp rsp (+ operand-size imm16) x86))
               ((when flg1) (mv flg1 0 x86)))
            (mv nil new-rsp x86))))
       ((when flg)
        (!!ms-fresh :imm-rml16-error flg))

       ;; For #xC3: We don't need to check for valid length for
       ;; one-byte instructions.  The length will be more than 15 only
       ;; if get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.
       ;; For #xC2:
       ((the (signed-byte #.*max-linear-address-size+2*) addr-diff)
        (if (equal opcode #xC2)
            (-
             ;; Adding 2 to account for imm16 in #xC2.
             (the (signed-byte #.*max-linear-address-size+1*)
                  (+ 2 temp-rip))
             (the (signed-byte #.*max-linear-address-size*)
                  start-rip))
          ;; Irrelevant for #xC3.
          0))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Note that instruction pointers are modeled as signed in 64-bit mode,
       ;; but unsigned in 32-bit mode.
       (check-alignment? (alignment-checking-enabled-p x86))
       ((mv flg (the (signed-byte 64) tos) x86)
        (if (= operand-size 8)
            (rime-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil)
          (rme-size operand-size rsp *ss* :r check-alignment? x86 :mem-ptr? nil)))
       ((when flg)
        (cond
         ((and (consp flg) (eql (car flg) :non-canonical-address))
          (!!fault-fresh :ss 0 :riml64-error flg)) ;; #SS(0)
         ((and (consp flg) (eql (car flg) :unaligned-linear-address))
          (!!fault-fresh :ac 0 :memory-access-unaligned rsp)) ;; #AC(0)
         (t ;; Unclassified error!
          (!!fault-fresh flg))))

       ;; Ensure that the return address is canonical (for 64-bit mode) and
       ;; within code segment limits (for 32-bit mode). It is not clear whether
       ;; this check should be performed here or deferred to when the next
       ;; instruction is fetched, but for now we do it here because this is the
       ;; approach taken in other parts of the model. It is in a way always
       ;; "safe" to stop execution with an error (in the sense that the model
       ;; provides no guarantees when this happens).
       ((unless (if (64-bit-modep x86)
                    (canonical-address-p tos)
                  (b* ((cs-hidden (xr :seg-hidden *cs* x86))
                       (cs.limit (hidden-seg-reg-layout-slice :limit cs-hidden)))
                    (and (<= 0 tos) (<= tos cs.limit)))))
        (!!ms-fresh :gp 0 :bad-return-address tos)) ;; #GP(0)

       ;; Update the x86 state:

       ;; Increment the stack pointer.
       (x86 (write-*sp new-rsp x86))

       ;; Update the rip to point to the return address.
       ;; The pseudocode for RET in Intel manual, Mar'17, Volume 2
       ;; says that a 16-bit return instruction pointer
       ;; should be zero-extended and stored into EIP.
       ;; Thus, we do not use WRITE-*IP here,
       ;; which has a different treatment for 16-bit instruction pointers.
       ;; This seems inconsistent, and it is an ambiguous aspect
       ;; of the Intel and AMD manuals.
       (x86 (!rip (the (signed-byte #.*max-linear-address-size*) tos) x86)))

    x86))

;; ======================================================================
;; INSTRUCTION: LEAVE
;; ======================================================================

(def-inst x86-leave

  ;; The LEAVE instruction releases the stack frame set up by an
  ;; earlier ENTER instruction.

  ;; Op/En: NP
  ;; C9
  ;; RSP := RBP
  ;; rBP := Pop() (i.e. get bytes from the stack, also considering the
  ;; operand-size override prefix, and put them in rBP, and then
  ;; increment the stack pointer appropriately)

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :implemented
  (add-to-implemented-opcodes-table 'LEAVE #xC9 '(:nil nil) 'x86-leave)

  :body

  (b* ((ctx 'x86-leave)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p3 (equal #.*operand-size-override*
                  (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 2 8) pop-bytes)
        (if p3
            2
          8))
       (rbp (rgfi *rbp* x86))
       ((when (not (canonical-address-p rbp)))
        (!!ms-fresh :rbp-not-canonical rbp))
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac? (not (equal (logand rbp 7) 0))))
        (!!ms-fresh :memory-access-unaligned rbp))
       ((mv flg val x86)
        (rml-size pop-bytes
                 (the (signed-byte #.*max-linear-address-size*) rbp)
                 :r x86))
       ((when flg)
        (!!ms-fresh :rml-size-error flg))
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rbp) pop-bytes))
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!ms-fresh :invalid-rsp new-rsp))

       ;; We don't need to check for valid length for one-byte
       ;; instructions.  The length will be more than 15 only if
       ;; get-prefixes fetches 15 prefixes, and that error will be
       ;; caught in x86-fetch-decode-execute, that is, before control
       ;; reaches this function.


       ;; Update the x86 state:
       ;; We chose to write the value val into the register using !rgfi-size
       ;; rather than !rgfi since val is a n64p value and !rgfi expects an i64p
       ;; value.

       (x86 (!rgfi-size pop-bytes *rbp* val rex-byte x86))
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
