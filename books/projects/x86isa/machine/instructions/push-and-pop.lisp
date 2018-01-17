;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; The documentation is ambiguous about the determination of the operand size of
; the PUSH and POP instructions in 64-bit mode.
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
       ((when lock)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

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

       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand
                                new-rsp
                                (the (integer 0 15)
                                  (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :new-rsp-not-aligned new-rsp)) ;; #AC(0)

       ;; See "Z" in http://ref.x86asm.net/geek.html#x50
       (reg (mbe :logic (loghead 3 opcode)
                 :exec (the (unsigned-byte 3)
                         (logand #x07 opcode))))
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (val (rgfi-size operand-size (reg-index reg rex-byte #.*b*) rex-byte
                       x86))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  val
                  x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)

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

(def-inst x86-push-Ev
  :parents (one-byte-opcodes)

  :short "PUSH: FF/6 r/m"
  :long "<p>Op/En: M</p>
   <p><tt>FF/6 r/m</tt></p>
   <p>Note that <tt>FF/6 r/m32</tt> is N.E. in the 64-bit mode.</p>

<p>PUSH doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>

<p>This opcode belongs to Group 5, and it has an opcode
extension (ModR/m.reg = 6).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn (add-to-implemented-opcodes-table 'PUSH #xFF '(:reg 6) 'x86-push-Ev))

  :body

  (b* ((ctx 'x86-push-Ev)
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))
       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          ;; See http://www.x86-64.org/documentation/assembly.html
          8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
        (!!fault-fresh :ss 0 :new-rsp-not-canonical new-rsp)) ;; #SS(0)
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand
                                new-rsp
                                (the (integer 0 15)
                                  (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :new-rsp-not-aligned new-rsp)) ;; #AC(0)

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?E-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*rgf-access* operand-size
         ;; inst-ac? is nil here because we only need increment-RIP-by
         ;; from this function.
         nil
         nil ;; Not a memory pointer operand
         p2 p4? temp-rip rex-byte r/m mod sib
         0 ;; No immediate operand
         x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ increment-RIP-by temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!fault-fresh :gp 0 :temp-rip-not-canonical temp-rip)) ;; #GP(0)
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:

       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  E
                  x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

    x86))

(def-inst x86-push-I

  :parents (one-byte-opcodes)

  :short "PUSH: 6A/68 ib/iw/id"

  :long "<p>Op/En: I</p>
   <p><tt>6A ib</tt>: PUSH imm8</p>
   <p><tt>68 iw</tt>: PUSH imm16</p>
   <p><tt>68 id</tt>: PUSH imm32</p>

<p>From the description of the PUSH instruction \(Intel Manual,
Vol. 2, Section 4.2\):</p>

<p><i> If the source operand is an immediate of size less than the
 operand size, a sign-extended value is pushed on the stack.</i></p>

<p>PUSH doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :guard-hints (("Goal" :in-theory (e/d* () ())))

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x68 '(:nil nil)
                                      'x86-push-I)
    (add-to-implemented-opcodes-table 'PUSH #x6A '(:nil nil)
                                      'x86-push-I))

  :body

  (b* ((ctx 'x86-push-I)
       (lock (eql #.*lock*
                  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) imm-size)
        (if (equal opcode #x6A)
            1
          (if (logbitp #.*w* rex-byte)
              4
            (if p3?
                2
              4))))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          ;; See http://www.x86-64.org/documentation/assembly.html
          8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
        (!!fault-fresh :ss 0 :new-rsp-not-canonical new-rsp)) ;; #SS(0)

       ((mv flg0 (the (signed-byte 32) imm) x86)
        (riml-size imm-size temp-rip :x x86))
       ((when flg0)
        (!!ms-fresh :imm-riml-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ imm-size temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!fault-fresh :gp 0 :temp-rip-not-canonical temp-rip)) ;; #GP(0)

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:

       ((mv flg1 x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  (mbe :logic (loghead (ash operand-size 3) imm)
                       :exec (logand
                              (case operand-size
                                (2 #.*2^16-1*)
                                (8 #.*2^64-1*))
                              (the (signed-byte 32) imm)))
                  x86))
       ((when flg1) ;; Would also handle "bad" rsp values.
        (!!fault-fresh :ss 0 :SS-exception-wme-size-error flg1)) ;; #SS(0)
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))

      x86))

(def-inst x86-push-segment-register
  :parents (two-byte-opcodes)

  :short "PUSH FS/GS"
  :long "<p><tt>0F A0</tt>: \[PUSH FS\]</p>
<p><tt>0F A8</tt>: \[PUSH GS\]</p>
   <p>Pushing other segment registers in the 64-bit mode is
   invalid.</p>

<p>If the source operand is a segment register \(16 bits\) and the
 operand size is 64-bits, a zero- extended value is pushed on the
 stack; if the operand size is 32-bits, either a zero-extended value
 is pushed on the stack or the segment selector is written on the
 stack using a 16-bit move. For the last case, all recent Core and
 Atom processors perform a 16-bit move, leaving the upper portion of
 the stack location unmodified.</p>

<p>PUSH doesn't have a separate instruction semantic function, unlike
other opcodes like ADD, SUB, etc. I've just coupled the decoding with
the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'PUSH #x0FA0 '(:nil nil)
                                      'x86-push-segment-register)
    (add-to-implemented-opcodes-table 'PUSH #x0FA8 '(:nil nil)
                                      'x86-push-segment-register))

  :body

  (b* ((ctx 'x86-push-general-register)
       (lock (eql #.*lock*
                  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          ;; See http://www.x86-64.org/documentation/assembly.html
          8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
        (!!fault-fresh :ss 0 :new-rsp-not-canonical new-rsp)) ;; #SS(0)

       ((the (unsigned-byte 16) val)
        (seg-visiblei (if (eql opcode #xA0) *FS* *GS*) x86))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:

       ((mv flg x86)
        (wme-size operand-size
                  (the (signed-byte #.*max-linear-address-size*) new-rsp)
                  *ss*
                  ;; If operand-size is 64, val is zero-extended here
                  ;; automatically.
                  val
                  x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!fault-fresh :ss 0 :SS-error-wme-size-error flg)) ;; #SS(0)

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

      x86))

;; ======================================================================
;; INSTRUCTION: (one-byte opcode map)
;; pop
;; ======================================================================

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
       ((when lock)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

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
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp (the (integer 0 15)
                                                (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :rsp-not-aligned rsp)) ;; #AC(0)

       ((mv flg new-rsp) (add-to-*sp rsp operand-size x86))
       ((when flg) (!!fault-fresh :ss 0 :pop flg)) ;; #SS(0)

       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r x86))
       ((when flg0)
        (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; #SS(0)

       ;; See "Z" in http://ref.x86asm.net/geek.html#x58.
       (reg (logand opcode #x07))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

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

(def-inst x86-pop-Ev
  :parents (one-byte-opcodes)

  :short "POP: 8F/0 r/m"

  :long "<p>Op/En: M</p>
   <p><tt>8F/0 r/m</tt></p>
   <p>Note that <tt>8F/0 r/m32</tt> is N.E. in the 64-bit mode.</p>

<p>POP doesn't have a separate instruction semantic function,
unlike other opcodes like ADD, SUB, etc. I've just coupled the
decoding with the execution in this case.</p>

<p>This opcode belongs to Group 1A, and it has an opcode
extension (ModR/m.reg = 0).</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'POP #x8F '(:reg 0) 'x86-pop-Ev)

  :body

  (b* ((ctx 'x86-pop-Ev)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p3 (equal #.*operand-size-override*
                  (prefixes-slice :group-3-prefix prefixes)))
       (p4? (equal #.*addr-size-override*
                   (prefixes-slice :group-4-prefix prefixes)))

       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))

       ((the (integer 1 8) operand-size)
        (if p3
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          8))

       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
        (!!fault-fresh :ss 0 :rsp-not-canonical rsp)) ;; #SS(0)
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :rsp-not-aligned rsp)) ;; #AC(0)

       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!fault-fresh :ss 0
                       :ss-exception-new-rsp-not-canonical new-rsp)) ;; #SS(0)

       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r x86))
       ((when flg0)
        (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; # SS(0)

       ((mv flg1 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib
                              0 ;; No immediate operand
                              x86)))
       ((when flg1) ;; #SS exception?
        (!!ms-fresh :x86-effective-addr-error flg1))

       ((mv flg2 v-addr)
        (case p2
          (0 (mv nil v-addr))
          ;; I don't really need to check whether FS and GS base are
          ;; canonical or not.  On the real machine, if the MSRs
          ;; containing these bases are assigned non-canonical
          ;; addresses, an exception is raised.
          (#.*fs-override*
           (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
                  (fs-base (n64-to-i64 nat-fs-base)))
             (if (not (canonical-address-p fs-base))
                 (mv 'Non-Canonical-FS-Base fs-base)
               (mv nil (+ fs-base v-addr)))))
          (#.*gs-override*
           (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
                  (gs-base (n64-to-i64 nat-gs-base)))
             (if (not (canonical-address-p gs-base))
                 (mv 'Non-Canonical-GS-Base gs-base)
               (mv nil (+ gs-base v-addr)))))
          (t (mv 'Unidentified-P2 v-addr))))
       ((when flg2)
        (!!ms-fresh :Fault-in-FS/GS-Segment-Addressing flg2))
       ((when (not (canonical-address-p v-addr)))
        (!!ms-fresh :v-addr-not-canonical v-addr))

       ((mv flg3 x86)
        (x86-operand-to-reg/mem
         operand-size inst-ac?
         nil ;; Not a memory pointer operand
         val v-addr rex-byte r/m mod x86))
       ((when flg3)
        (!!ms-fresh :x86-operand-to-reg/mem flg2))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ increment-RIP-by temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       ;; If the instruction goes beyond 15 bytes, stop. Change to an
       ;; exception later.
       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))

       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86 (!rip temp-rip x86)))

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
       ((when lock?)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
        (!!fault-fresh :ss 0 :new-rsp-not-canonical new-rsp)) ;; #SS(0)
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand new-rsp
                                       (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :new-rsp-not-aligned new-rsp)) ;; #AC(0)

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
                  x86))
       ((when flg)
        (!!fault-fresh :ss 0 :wme-size-error flg)) ;; #SS(0)
       (x86 (!rip temp-rip x86))
       (x86 (!rgfi *rsp* new-rsp x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: POPF/POPFQ
;; ======================================================================

(def-inst x86-popf

  ;; #x9D
  ;; Op/En: NP

  ;; Intel Vol. 2B, p. 4-350 says: "In 64-bit mode, use REX.w to pop
  ;; the top of stack to RFLAGS.  POPFQ pops 64-bits from the stack,
  ;; loads the lower 32 bits into rflags, and zero-extends the upper
  ;; bits of eflags."

  ;; TO-DO@Shilpi: For the time being, I am going to assume that the
  ;; CPL is 0.

  ;; 64-bit mode operation of x86-popf:

  ;; if cpl > 0 then

  ;;    if operand-size = 8 then

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
       ((when lock?)
        (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          8))
       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
        (!!fault-fresh :ss 0 :rsp-not-canonical rsp)) ;; #SS(0)
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp
                                       (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!fault-fresh :ac 0 :rsp-not-aligned rsp)) ;; #AC(0)
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!fault-fresh :ss 0
                       :ss-exception-new-rsp-not-canonical new-rsp)) ;; #SS(0)

       ((mv flg0 val x86)
        (rme-size operand-size rsp *ss* :r x86))
       ((when flg0)
        (!!fault-fresh :ss 0 :rme-size-error flg0)) ;; #SS(0)

       ((the (unsigned-byte 32) val)
        ;; All reserved bits should be unaffected.  This ensures that the bit 1
        ;; of rflags is set, and bits 3, 5, 15, and 22-63 are cleared.
        (logior 2 (the (unsigned-byte 32) (logand #x3f7fd7 val))))

       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
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

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: PUSHA/PUSHAD
;; ======================================================================

;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.

(def-inst x86-pusha

  :parents (one-byte-opcodes)

  :short "PUSHA/PUSHAD: 60"

  :long
  "<p>
   This is invalid in 64-bit mode.
   It throws a #UD exception.
   </p>"

  :implemented
  (add-to-implemented-opcodes-table 'pusha #x60 '(:nil nil) 'x86-pusha)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body
  (b* ((ctx 'x86-pusha))
    (!!fault-fresh :ud nil))) ;; #UD

;; ======================================================================
;; INSTRUCTION: POPA/POPAD
;; ======================================================================

;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.

(def-inst x86-popa

  :parents (one-byte-opcodes)

  :short "POPA/POPD: 61"

  :long
  "<p>
   This is invalid in 64-bit mode.
   It throws a #UD exception.
   </p>"

  :implemented
  (add-to-implemented-opcodes-table 'popa #x61 '(:nil nil) 'x86-popa)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))

  :body
  (b* ((ctx 'x86-popa))
    (!!fault-fresh :ud nil))) ;; #UD

;; ======================================================================
