;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "multiply-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: MUL
;; ======================================================================

(def-inst x86-mul

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 4 when this function
  ;; is called.

  :guard (equal (mrm-reg modr/m) 4)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/4: MUL r/m8:  AX := AL \* r/m8</p>
  <p>F7/4: MUL r/m16: DX:AX := AX \* r/m16<br/>
        MUL r/m32: EDX:EAX := EAX \* r/m32<br/>
        MUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'MUL #xF6 '(:reg 4)
                                      'x86-mul)
    (add-to-implemented-opcodes-table 'MUL #xF7 '(:reg 4)
                                      'x86-mul))
  :body

  (b* ((ctx 'x86-mul)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size
         select-byte-operand rex-byte nil prefixes))

       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
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

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))

       ;; Computing the result:
       ((mv product-high product-low product)
        (mul-spec reg/mem-size rAX reg/mem))

       ;; Updating the x86 state:

       (x86
        (case reg/mem-size
          (1 ;; AX := AL * r/m8
           (let* ((x86 (!rgfi-size 2 *rax* product rex-byte x86)))
             x86))
          (otherwise
           (let* ((x86 ;; Write to rAX
                   (!rgfi-size reg/mem-size *rax* product-low
                               rex-byte x86))
                  (x86 ;; Write to rDX
                   (!rgfi-size reg/mem-size *rdx* product-high
                               rex-byte x86)))
             x86))))

       (x86
        (if (equal product-high 0)
            (let* ((x86 (!flgi #.*cf* 0 x86))
                   (x86 (!flgi-undefined #.*pf* x86))
                   (x86 (!flgi-undefined #.*af* x86))
                   (x86 (!flgi-undefined #.*zf* x86))
                   (x86 (!flgi-undefined #.*sf* x86))
                   (x86 (!flgi #.*of* 0 x86)))
              x86)
          (let* ((x86 (!flgi #.*cf* 1 x86))
                 (x86 (!flgi-undefined #.*pf* x86))
                 (x86 (!flgi-undefined #.*af* x86))
                 (x86 (!flgi-undefined #.*zf* x86))
                 (x86 (!flgi-undefined #.*sf* x86))
                 (x86 (!flgi #.*of* 1 x86)))
            x86)))

       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: IMUL
;; ======================================================================

(def-inst x86-imul-Op/En-M

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'IMUL #xF6 '(:reg 5)
                                      'x86-imul-Op/En-M)
    (add-to-implemented-opcodes-table 'IMUL #xF7 '(:reg 5)
                                      'x86-imul-Op/En-M))


  ;; Note that the reg field serves as an opcode extension for this
  ;; instruction.  The reg field will always be 5 when this function is
  ;; called.

  :guard (equal (mrm-reg modr/m) 5)

  :long
  "<h4>Op/En: M</h4>

  <p>F6/5: <br/>
     IMUL r/m8:  AX      := AL  \* r/m8<br/><br/>

     F7/5: <br/>
     IMUL r/m16: DX:AX   := AX  \* r/m16<br/>
     IMUL r/m32: EDX:EAX := EAX \* r/m32<br/>
     IMUL r/m64: RDX:RAX := RAX \* r/m64<br/></p>"

  :body

  (b* ((ctx 'x86-imul-Op/En-M)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (equal opcode #xF6))
       ((the (integer 1 8) reg/mem-size)
        (select-operand-size select-byte-operand rex-byte nil prefixes))

       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by) ?v-addr x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
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

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Computing the result:
       (rAX (rgfi-size reg/mem-size *rax* rex-byte x86))
       ((mv product-high product-low product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size rAX reg/mem))

       ;; Updating the x86 state:
       (x86
        (case reg/mem-size
          (1 ;; AX := AL * r/m8
           (let* ((x86 (!rgfi-size 2 *rax* product rex-byte x86)))
             x86))
          (otherwise
           (let* ((x86 ;; Write to rAX
                   (!rgfi-size reg/mem-size *rax* product-low
                               rex-byte x86))
                  (x86 ;; Write to rDX
                   (!rgfi-size reg/mem-size *rdx* product-high
                               rex-byte x86)))
             x86))))

       (x86
        (let* ((x86 (!flgi #.*cf* cf-and-of x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*zf* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi #.*of* cf-and-of x86)))
          x86))

       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-imul-Op/En-RM

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  :implemented
  (add-to-implemented-opcodes-table 'IMUL #x0FAF '(:nil nil)
                                    'x86-imul-Op/En-RM)

  :long
  "<h4>Op/En: RM</h4>

  <p>0F AF:<br/>
     IMUL r16, r/m16: r16 := r16 \* r/m16 <br/>
     IMUL r32, r/m32: r32 := r32 \* r/m32 <br/>
     IMUL r64, r/m64: r64 := r64 \* r/m64 <br/> </p>"

  :body

  (b* ((ctx 'x86-imul-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) reg/mem-size)
        (select-operand-size nil rex-byte nil prefixes))
       (inst-ac? t)
       ((mv flg0 reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
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
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       (register (rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
                            rex-byte x86))

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size reg/mem register))

       ;; Updating the x86 state:
       (x86
        (!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
                    product-low rex-byte x86))

       (x86
        (let* ((x86 (!flgi #.*cf* cf-and-of x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*zf* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi #.*of* cf-and-of x86)))
          x86))

       (x86 (!rip temp-rip x86)))
    x86))

(def-inst x86-imul-Op/En-RMI

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  :long
  "<h4>Op/En: RMI</h4>

  <p>6B ib:<br/>
      IMUL r16, r/m16, imm8<br/>
      IMUL r32, r/m32, imm8 <br/>
      IMUL r64, r/m64, imm8 <br/> <br/>

      69 iw:<br/>
      IMUL r16, r/m16, imm16 <br/>
      IMUL r32, r/m32, imm32 <br/>
      IMUL r64, r/m64, imm32 <br/> </p>"

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSHF #x69 '(:nil nil)
                                      'x86-imul-Op/En-RMI)
    (add-to-implemented-opcodes-table 'PUSHF #x6B '(:nil nil)
                                      'x86-imul-Op/En-RMI))

  :body

  (b* ((ctx 'x86-imul-Op/En-RMI)
       (r/m (the (unsigned-byte 3) (mrm-r/m modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg modr/m)))

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       ((the (integer 1 8) reg/mem-size)
        (select-operand-size nil rex-byte nil prefixes))

       ((the (integer 1 4) imm-size)
        (if (equal opcode #x6B)
            1
          ;; opcode = #x69
          (if (equal reg/mem-size 2)
              2
            4)))
       (inst-ac? t)
       ((mv flg0 reg/mem
            (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*gpr-access* reg/mem-size inst-ac?
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         imm-size ;; imm-size bytes of immediate data
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
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg1 (the (unsigned-byte 32) imm) x86)
        (rml-size imm-size temp-rip :x x86))
       ((when flg1)
        (!!ms-fresh :riml-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip imm-size))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Computing the result:
       ((mv ?product-high product-low ?product (the (unsigned-byte 1) cf-and-of))
        (imul-spec reg/mem-size reg/mem imm))

       ;; Updating the x86 state:
       (x86
        (!rgfi-size reg/mem-size (reg-index reg rex-byte #.*r*)
                    product-low rex-byte x86))


       (x86
        (let* ((x86 (!flgi #.*cf* cf-and-of x86))
               (x86 (!flgi-undefined #.*pf* x86))
               (x86 (!flgi-undefined #.*af* x86))
               (x86 (!flgi-undefined #.*zf* x86))
               (x86 (!flgi-undefined #.*sf* x86))
               (x86 (!flgi #.*of* cf-and-of x86)))
          x86))

       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
