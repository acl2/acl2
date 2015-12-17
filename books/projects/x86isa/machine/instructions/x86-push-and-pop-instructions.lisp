;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: (one- and two- byte opcode maps)
;; push
;; ======================================================================

(def-inst x86-push-general-register
  :parents (one-byte-opcodes)

  :short "PUSH: 50+rw/rd"
  :long "<p>Op/En: O</p>
   <p><tt>50+rw/rd r16/r64</tt>: \[PUSH E\]</p>
   <p>Note that <tt>50+rd r32</tt> is N.E. in the 64-bit mode.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :body

  (b* ((ctx 'x86-push-general-register)
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

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
        (!!ms-fresh :new-rsp-not-canonical new-rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand
                                new-rsp
                                (the (integer 0 15)
                                  (- operand-size 1)))
                               0))))
        (!!ms-fresh :new-rsp-not-aligned new-rsp)) ;; #AC

       ;; See "Z" in http://ref.x86asm.net/geek.html#x50
       (reg (mbe :logic (loghead 3 opcode)
                 :exec (the (unsigned-byte 3)
                         (logand #x07 opcode))))
       ;; See Intel Table 3.1, p.3-3, Vol. 2-A
       (val (rgfi-size operand-size (reg-index reg rex-byte #.*b*) rex-byte
                       x86))

       ;; Update the x86 state:
       ((mv flg x86)
        (wm-size operand-size
                 (the (signed-byte #.*max-linear-address-size*) new-rsp)
                 val x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!ms-fresh :SS-error-wm-size-error flg))

       (x86 (!rgfi *rsp* (the (signed-byte #.*max-linear-address-size*) new-rsp) x86))
       (x86 (!rip temp-rip x86)))

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
        (!!ms-fresh :lock-prefix prefixes))

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
        (!!ms-fresh :new-rsp-not-canonical new-rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand
                                new-rsp
                                (the (integer 0 15)
                                  (- operand-size 1)))
                               0))))
        (!!ms-fresh :new-rsp-not-aligned new-rsp)) ;; #AC

       ((mv flg0 E (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) ?E-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         ;; inst-ac? is nil here because we only need increment-RIP-by
         ;; from this function.
         #.*rgf-access* operand-size nil p2 p4? temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ increment-RIP-by temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))
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
        (wm-size operand-size
                 (the (signed-byte #.*max-linear-address-size*) new-rsp)
                 E x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!ms-fresh :SS-error-wm-size-error flg))

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
        (!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 1 8) imm-size)
        (if (equal opcode #x6A)
            1
          (if p3? 2 4)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          ;; See http://www.x86-64.org/documentation/assembly.html
          8))
       (rsp (rgfi *rsp* x86))
       (new-rsp (- rsp operand-size))
       ((when (not (canonical-address-p new-rsp)))
        (!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((mv flg0 (the (signed-byte 32) imm) x86)
        (rim-size imm-size temp-rip :x x86))
       ((when flg0)
        (!!ms-fresh :imm-rim-size-error flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ imm-size temp-rip))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

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
        (wm-size operand-size
                 (the (signed-byte #.*max-linear-address-size*) new-rsp)
                 (mbe :logic (loghead (ash operand-size 3) imm)
                      :exec (logand
                             (case operand-size
                               (2 #.*2^16-1*)
                               (8 #.*2^64-1*))
                             (the (signed-byte 32) imm)))
                 x86))
       ((when flg1) ;; Would also handle "bad" rsp values.
        (!!ms-fresh :SS-exception-wm-size-error flg1))
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
        (!!ms-fresh :lock-prefix prefixes))

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
        (!!ms-fresh :new-rsp-not-canonical new-rsp))

       ((the (unsigned-byte 16) val)
        (seg-visiblei (if (eql opcode #xA0) *FS* *GS*) x86))

       ;; Update the x86 state:

       ((mv flg x86)
        (wm-size operand-size
                 (the (signed-byte #.*max-linear-address-size*)
                   new-rsp)
                 ;; If operand-size is 64, val is zero-extended here
                 ;; automatically.
                 val x86))
       ((when flg) ;; Would also handle bad rsp values.
        (!!ms-fresh :SS-error-wm-size-error flg))

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
   <p><tt>58+rw/rd r16/r64</tt>: \[POP E\]</p>
   <p>Note that <tt>58+rd r32</tt> is N.E. in the 64-bit mode.</p>

<p>POP doesn't have a separate instruction semantic function, unlike
other opcodes like ADD, SUB, etc. I've just coupled the decoding with
the execution in this case.</p>"

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :body

  (b* ((ctx 'x86-pop-general-register)
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       (p3? (eql #.*operand-size-override*
                 (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          ;; See http://www.x86-64.org/documentation/assembly.html
          8))
       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
        (!!ms-fresh :rsp-not-canonical rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!ms-fresh :rsp-not-aligned rsp)) ;; #AC

       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
        (rm-size operand-size rsp :r x86))
       ((when flg0)
        (!!ms-fresh :rm-size-error flg0))

       ;; See "Z" in http://ref.x86asm.net/geek.html#x58.
       (reg (logand opcode #x07))
       ;; Update the x86 state:
       (x86 (!rgfi *rsp* new-rsp x86))
       (x86
        ;; See Intel Table 3.1, p.3-3, Vol. 2-A
        (!rgfi-size operand-size (reg-index reg rex-byte #.*b*)
                    val rex-byte x86))
       (x86 (!rip temp-rip x86)))

    x86)

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
        (!!ms-fresh :lock-prefix prefixes))
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
        (!!ms-fresh :rsp-not-canonical rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!ms-fresh :rsp-not-aligned rsp)) ;; #AC

       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
        (rm-size operand-size rsp :r x86))
       ((when flg0)
        (!!ms-fresh :rm-size-error flg0))

       ((mv flg1 (the (signed-byte 64) v-addr) (the (unsigned-byte 3) increment-RIP-by) x86)
        (if (equal mod #b11)
            (mv nil 0 0 x86)
          (x86-effective-addr p4? temp-rip rex-byte r/m mod sib 0 x86)))
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
         operand-size inst-ac? val v-addr rex-byte r/m mod x86))
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

      x86))

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
;;         (rm-size operand-size rsp :r x86))
;;        ((when flg0) ;; #SS exception?
;;         (!!ms-fresh :rm-size-error flg0))

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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'PUSHF #x9C '(:nil nil) 'x86-pushf)

  :body

  (b* ((ctx 'x86-pushf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
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
        (!!ms-fresh :new-rsp-not-canonical new-rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand new-rsp (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!ms-fresh :new-rsp-not-aligned new-rsp)) ;; #AC

       ((the (unsigned-byte 32) eflags) (rflags x86))

       ((the (unsigned-byte 32) eflags)
        (case operand-size
          ;; Lower 16 bits are stored on the stack
          (2 (logand #xffff eflags))
          ;; VM and RF rflag bits are cleared in the image stored on the
          ;; stack.  Also, bits from 22-63 are reserved, and hence,
          ;; zeroed out.
          (otherwise (logand #x3cffff eflags))))

       ;; Update the x86 state:
       ((mv flg x86)
        (wm-size operand-size
                 (the (signed-byte #.*max-linear-address-size*) new-rsp)
                 eflags x86))
       ((when flg)
        (!!ms-fresh :wm-size-error flg))
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
  :guard-hints (("Goal" :in-theory (e/d (rim08 rim32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'POPF #x9D '(:nil nil) 'x86-popf)

  :body

  (b* ((ctx 'x86-popf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?)
        (!!ms-fresh :lock-prefix prefixes))
       (p3? (equal #.*operand-size-override*
                   (prefixes-slice :group-3-prefix prefixes)))
       ((the (integer 1 8) operand-size)
        (if p3?
            2
          ;; 4-byte operand size is N.E. in 64-bit mode
          8))
       (rsp (rgfi *rsp* x86))
       ((when (not (canonical-address-p rsp)))
        (!!ms-fresh :rsp-not-canonical rsp)) ;; #SS
       (inst-ac? (alignment-checking-enabled-p x86))
       ((when (and inst-ac?
                   (not (equal (logand rsp (the (integer 0 15) (- operand-size 1)))
                               0))))
        (!!ms-fresh :rsp-not-aligned rsp)) ;; #AC
       ((the (signed-byte #.*max-linear-address-size+1*) new-rsp)
        (+ (the (signed-byte #.*max-linear-address-size*) rsp) operand-size))
       ;; Raise a #SS exception.
       ((when (mbe :logic (not (canonical-address-p new-rsp))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               new-rsp))))
        (!!ms-fresh :ss-exception-new-rsp-not-canonical new-rsp))

       ((mv flg0 val x86)
        (rm-size operand-size rsp :r x86))
       ((when flg0)
        (!!ms-fresh :rm-size-error flg0))

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

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
