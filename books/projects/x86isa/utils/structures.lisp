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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Robert Krug         <rkrug@cs.utexas.edu>

(in-package "X86ISA")

(include-book "utilities")
(include-book "basic-structs")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(std::make-define-config
 :no-function t
 :inline t)

;; ----------------------------------------------------------------------

(defsection structures
  :parents (utils)
  :short "<b>@('x86')-specific bit structures</b>"

  :long "<p>We define some bitstructures using @(see fty::defbitstruct) to
  describe the fields of registers and x86 data structures.</p>" )

(local (xdoc::set-default-parents structures))

;; ----------------------------------------------------------------------

;; We add "Bits" as a suffix for all bitstructs other than the decoding-related
;; ones and the basic ones in basic-structs.lisp.  The reason is that
;; otherwise, the names of these other bitstructs may clash with x86 state
;; accessor functions (e.g., rflags, mxcsr, etc.).

;; Decoding-related Structures:

(defsection legacy-prefixes-layout-structure

  :short "Functions to collect legacy prefix bytes from an x86 instruction"

  :long "<p>The field @('num') of @('prefixes') not only includes the number of
  legacy prefixes present in an instruction, but also the number of REX bytes,
  even though REX bytes are not stored in this structure.  See @(tsee
  get-prefixes) for details.</p>"

  (defbitstruct prefixes
    ((num         4bits "Number of Prefix Bytes")
     (lck         8bits "Lock Prefix")
     (rep         8bits "Repeat Prefix")
     (seg         8bits "Segment Override Prefix")
     (opr         8bits "Operand-Size Override Prefix")
     (adr         8bits "Address-Size Override Prefix")
     (nxt         8bits "First non-prefix instruction byte"))
    :inline t)

  (local
   (defthm prefixes-layout-ok
     (iff (prefixes-p x)
          (unsigned-byte-p *prefixes-width* x))
     :rule-classes nil)))

(defsection vex-prefixes-layout-structures

  :short "Functions to decode and collect VEX prefix bytes from an x86
  instruction"

  (defbitstruct vex-prefixes
    ((byte0  8bits "Can either be #xC4 or #xC5")
     (byte1  8bits "Byte 1 of VEX prefixes")
     (byte2  8bits "Relevant only for 3-byte VEX prefixes"))
    :inline t)

  (local
   (defthm vex-prefixes-layout-ok
     (iff (vex-prefixes-p x)
          (unsigned-byte-p *vex-width* x))
     :rule-classes nil))

  (define vex-prefixes-byte0-p ((vex-prefixes vex-prefixes-p))
    :short "Returns @('t') if byte0 of the @('vex-prefixes') structure is
    either @('*vex2-byte0*') or @('*vex3-byte0*'); returns @('nil') otherwise"
    :returns (ok booleanp)
    (let ((byte0 (vex-prefixes->byte0 vex-prefixes)))
      (or (equal byte0 #.*vex2-byte0*) (equal byte0 #.*vex3-byte0*))))

  ;; From Intel Vol. 2, Section 2.3.5.6: "In 32-bit mode the VEX first
  ;; byte C4 and C5 alias onto the LES and LDS instructions. To
  ;; maintain compatibility with existing programs the VEX 2nd byte,
  ;; bits [7:6] must be 11b."

  ;; So, in 32-bit mode, *vex2-byte1-layout* must have r and MSB of
  ;; vvvv set to 1, and *vex3-byte1-layout* must have r and x set to 1
  ;; if VEX is to be used instead of LES/LDS.

  ;; "If an instruction does not use VEX.vvvv then it should be set to
  ;; 1111b otherwise instruction will #UD.  In 64-bit mode all 4 bits
  ;; may be used. See Table 2-8 for the encoding of the XMM or YMM
  ;; registers. In 32-bit and 16-bit modes bit 6 must be 1 (if bit 6
  ;; is not 1, the 2-byte VEX version will generate LDS instruction
  ;; and the 3-byte VEX version will ignore this bit)."

  ;; The above is reason why only 8 XMM/YMM registers are available in
  ;; 32- and 16-bit modes.

  ;; Source for VEX layout constants:
  ;; Intel Vol. 2 (May 2018), Figure 2-9 (VEX bit fields)

  ;; Note that the 2-byte VEX implies a leading 0F opcode byte, and
  ;; the 3-byte VEX implies leading 0F, 0F 38, or 0F 3A bytes.

  (defbitstruct vex2-byte1
    ((pp 2bits
         "Opcode extension providing equivalent functionality of a SIMD
          prefix; <br/>
         @('#b00 - None; #b01 - #x66; #b10 - #xF3; #b11 - #xF2')")
     (l  bitp
         "Vector Length; <br/>
          @('0 - scalar or 128-bit vector; 1 - 256-bit vector')")
     (vvvv 4bits
           "A register specifier (in 1's complement form) or @('1111') if
           unused.")
     (r    bitp
           "@('REX.R') in 1's complement (inverted) form;<br/>
      @('1: Same as REX.R=0 (must be 1 in 32-bit mode);')<br/>
      @('0: Same as REX.R=1 (64-bit mode only)').<br/>
      In protected and compatibility modes, the bit must be set to @('1'),
      otherwise the instruction is LES or LDS."))
    :msb-first nil
    :inline t)

  (defbitstruct vex3-byte1
    ((m-mmmm 5bits
             "@('00000'): Reserved for future use (will #UD) <br/>
              @('00001'): implied 0F leading opcode byte
              @('00010'): implied 0F 38 leading opcode bytes
              @('00011'): implied 0F 3A leading opcode bytes
              @('00100-11111'): Reserved for future use (will #UD)")
     (b bitp
        "REX.B in 1's complement (inverted) form <br/>
         @('1 - Same as REX.B=0') (Ignored in 32-bit mode) <br/>
         @('0 - Same as REX.B=1') (64-bit mode only)")
     (x bitp
        "REX.X in 1's complement (inverted) form <br/>
         @('1 - Same as REX.X=0') (must be 1 in 32-bit mode) <br/>
         @('0 - Same as REX.X=1') (64-bit mode only) <br/>
         In 32-bit modes, this bit must be set to @('1'), otherwise the
         instruction is LES or LDS.")
     (r bitp
        "REX.R in 1's complement (inverted) form <br/>
         @('1 - Same as REX.R=0') (must be 1 in 32-bit mode) <br/>
         @('0 - Same as REX.R=1') (64-bit mode only) <br/>
          In protected and compatibility modes the bit must be set to @('1')
          otherwise the instruction is LES or LDS."))
    :xvar vex3byte1
    :msb-first nil
    :inline t)

  (defbitstruct vex3-byte2
    ((pp 2bits
         "Opcode extension providing equivalent functionality of a SIMD
          prefix<br />
           @('#b00: None') <br />
           @('#b01: #x66') <br />
           @('#b10: #xF3') <br />
           @('#b11: #xF2')")

     (l bitp
        "Vector Length <br />
          @('0: scalar or 128-bit vector') <br />
          @('1: 256-bit vector')")

     (vvvv 4bits
           "A register specifier (in 1's complement form) or @('1111') if
             unused.")

     (w bitp
        "Opcode specific (use like REX.W, or used for opcode extension, or
          ignored, depending on the opcode byte" ))
    :msb-first nil
    :inline t)

  (define vex-prefixes-map-p ((bytes :type (unsigned-byte 16))
                              (vex-prefixes vex-prefixes-p))
    :guard (and (vex-prefixes-byte0-p vex-prefixes)
                (or (equal bytes #ux0F)
                    (equal bytes #ux0F38)
                    (equal bytes #ux0F3A)))
    :returns (ok booleanp)
    :short "Returns @('t') if the @('vex-prefixes'), irrespective of whether
    they are two- or three-byte form, indicate the map that begins with the
    escape bytes @('bytes')"
    (b* ((byte0 (vex-prefixes->byte0 vex-prefixes))
         (byte1 (vex-prefixes->byte1 vex-prefixes)))
      (case bytes
        (#ux0F
         (or (equal byte0 #.*vex2-byte0*)
             (and (equal byte0 #.*vex3-byte0*)
                  (equal (vex3-byte1->m-mmmm byte1) #.*v0F*))))
        (otherwise
         (and (equal byte0 #.*vex3-byte0*)
              (if (equal bytes #ux0F38)
                  (equal (vex3-byte1->m-mmmm byte1) #.*v0F38*)
                (equal (vex3-byte1->m-mmmm byte1) #.*v0F3A*)))))))

  ;; Some convenient accessor functions for those fields of the VEX prefixes
  ;; that are common to both the two- and three-byte forms:

  (define vex->vvvv ((vex-prefixes vex-prefixes-p))
    :short "Get the @('VVVV') field of @('vex-prefixes'); cognizant of the two-
    or three-byte VEX prefixes form"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :returns (vvvv (unsigned-byte-p 4 vvvv)
                   :hyp (vex-prefixes-byte0-p vex-prefixes)
                   :hints (("Goal" :in-theory (e/d (vex-prefixes-byte0-p) ()))))
    (case (vex-prefixes->byte0 vex-prefixes)
      (#.*vex2-byte0*
       (vex2-byte1->vvvv (vex-prefixes->byte1 vex-prefixes)))
      (#.*vex3-byte0*
       (vex3-byte2->vvvv (vex-prefixes->byte2 vex-prefixes)))
      (otherwise -1)))

  (define vex->l ((vex-prefixes :type (unsigned-byte #.*vex-width*)))
    :short "Get the @('L') field of @('vex-prefixes'); cognizant of the two- or
    three-byte VEX prefixes form"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :returns (l (unsigned-byte-p 1 l)
                :hyp (vex-prefixes-byte0-p vex-prefixes)
                :hints (("Goal" :in-theory (e/d (vex-prefixes-byte0-p) ()))))
    (case (vex-prefixes->byte0 vex-prefixes)
      (#.*vex2-byte0*
       (vex2-byte1->l (vex-prefixes->byte1 vex-prefixes)))
      (#.*vex3-byte0*
       (vex3-byte2->l (vex-prefixes->byte2 vex-prefixes)))
      (otherwise -1)))

  (define vex->pp ((vex-prefixes :type (unsigned-byte #.*vex-width*)))
    :short "Get the @('PP') field of @('vex-prefixes'); cognizant of the two- or
    three-byte VEX prefixes form"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :returns (pp (unsigned-byte-p 2 pp)
                 :hyp (vex-prefixes-byte0-p vex-prefixes)
                 :hints (("Goal" :in-theory (e/d (vex-prefixes-byte0-p) ()))))
    (case (vex-prefixes->byte0 vex-prefixes)
      (#.*vex2-byte0*
       (vex2-byte1->pp (vex-prefixes->byte1 vex-prefixes)))
      (#.*vex3-byte0*
       (vex3-byte2->pp (vex-prefixes->byte2 vex-prefixes)))
      (otherwise -1)))

  (define vex->w ((vex-prefixes :type (unsigned-byte #.*vex-width*)))
    :short "Get the @('W') field of @('vex-prefixes'); cognizant of the two- or
    three-byte VEX prefixes form"
    :guard (vex-prefixes-byte0-p vex-prefixes)
    :returns (w (unsigned-byte-p 1 w)
                :hyp (vex-prefixes-byte0-p vex-prefixes)
                :hints (("Goal" :in-theory (e/d (vex-prefixes-byte0-p) ()))))
    (case (vex-prefixes->byte0 vex-prefixes)
      (#.*vex3-byte0*
       (vex3-byte2->w (vex-prefixes->byte2 vex-prefixes)))
      ;; Source: Intel Vol. 2A, Section 3.1.1.2 --- Opcode Column in the
      ;; Instruction Summary Table (Instructions with VEX Prefix):
      ;; "The presence of W0 in the opcode column does not preclude the opcode
      ;; to be encoded using the C5H form of the VEX prefix, if the semantics
      ;; of the opcode does not require other VEX subfields not present in the
      ;; two-byte form of the VEX prefix."
      (otherwise 0))

    ///

    (defret if-not-vex3-byte0-then-vex-w=0
      (implies (not (equal (vex-prefixes->byte0 vex-prefixes) #.*vex3-byte0*))
               (equal (vex->w vex-prefixes) 0)))))

(defsection evex-prefixes-layout-structures

  :short "Functions to decode and collect EVEX prefix bytes from an x86
  instruction"

  ;; Sources: - Intel Vol. 2, Table 2-30
  ;;          - Sandpile, under "byte encodings" section:
  ;;            http://www.sandpile.org/x86/opc_enc.htm

  (defbitstruct evex-prefixes
    ((byte0      8bits) ;; Should be #ux62
     (byte1      8bits)
     (byte2      8bits)
     (byte3      8bits))
    :inline t
    :msb-first nil)

  (local
   (defthm evex-prefixes-layout-ok
     (iff (evex-prefixes-p x)
          (unsigned-byte-p *evex-width* x))
     :rule-classes nil))

  (defbitstruct evex-byte1
    ((mm 2bits
         "Identical to low two bits of VEX.m-mmmm.")
     (res 2bits "Reserved; must be zero." :default '0)
     (r-prime bitp
              "High-16 register specifier modifier -- combine with EVEX.R and
              ModR/M.reg.")

     ;; R, X, B are the next-8 register specifier
     ;; modifiers --- combine with ModR/M.reg,
     ;; ModR/M.r/m (base, index/vidx).
     (b bitp)
     (x bitp "Must be set to @('1') in 32-bit mode, otherwise instruction is
         BOUND.")
     (r bitp "Must be set to @('1') in 32-bit mode. otherwise instruction is
      BOUND."))
    :inline t
    :msb-first nil
    :xvar byte1)

  (defbitstruct evex-byte2
    ((pp 2bits "Compressed legacy escape -- identical to low two bits of VEX.pp.")
     (res bitp "Reserved; Must be one." :default '1)
     (vvvv 4bits "NDS register specifier --- same as VEX.vvvv.")
     (w bitp "Osize promotion/opcode extension"))
    :inline t
    :msb-first nil)

  (defbitstruct evex-byte3
    ((aaa 3bits "Embedded opmask register specifier")
     (v-prime bitp
              "High-16 NDS/VIDX register specifier -- combine with EVEX.vvvv or
      when VSIB present")
     (b bitp "Broadcast/RC/SAE Context")
     (vl/rc 2bits "Vector length/RC (denoted as L'L in the Intel manuals")
     (z bitp "Zeroing/Merging"))
    :inline t
    :msb-first nil)

  ;; Some wrapper functions to the macros above to make the EVEX dispatch
  ;; functions' guard proofs simpler:

  (define evex->aaa ((evex-prefixes evex-prefixes-p))
    :short "Get the @('aaa') field (embedded opmask) of @('evex-prefixes')"
    :returns (aaa (unsigned-byte-p 3 aaa) :hyp :guard)
    (evex-byte3->aaa (evex-prefixes->byte3 evex-prefixes)))

  (define evex->z ((evex-prefixes evex-prefixes-p))
    :short "Get the @('z') field (embedded opmask) of @('evex-prefixes')"
    :returns (z (unsigned-byte-p 1 z) :hyp :guard)
    (evex-byte3->z (evex-prefixes->byte3 evex-prefixes)))

  (define evex->vvvv ((evex-prefixes evex-prefixes-p))
    :short "Get the @('VVVV') field of @('evex-prefixes')"
    :returns (vvvv (unsigned-byte-p 4 vvvv) :hyp :guard)
    (evex-byte2->vvvv (evex-prefixes->byte2 evex-prefixes)))

  (define evex->v-prime ((evex-prefixes evex-prefixes-p))
    :short "Get the @('v-prime') field of @('evex-prefixes')"
    :returns (v-prime (unsigned-byte-p 1 v-prime) :hyp :guard)
    (evex-byte3->v-prime (evex-prefixes->byte3 evex-prefixes)))

  (define evex->vl/rc ((evex-prefixes evex-prefixes-p))
    :short "Get the @('vl/rc') field of @('evex-prefixes')"
    :returns (vl/rc (unsigned-byte-p 2 vl/rc) :hyp :guard)
    (evex-byte3->vl/rc (evex-prefixes->byte3 evex-prefixes)))

  (define evex->pp ((evex-prefixes evex-prefixes-p))
    :short "Get the @('PP') field of @('evex-prefixes')"
    :returns (pp (unsigned-byte-p 2 pp) :hyp :guard)
    (evex-byte2->pp (evex-prefixes->byte2 evex-prefixes)))

  (define evex->w ((evex-prefixes evex-prefixes-p))
    :short "Get the @('W') field of @('evex-prefixes')"
    :returns (w (unsigned-byte-p 1 w) :hyp :guard)
    (evex-byte2->w (evex-prefixes->byte2 evex-prefixes))))

(defsection ModR/M-structures
  :parents (ModR/M-decoding structures)
  :short "Bitstruct definitions to store a ModR/M byte and its fields"

  (local (xdoc::set-default-parents ModR/M-structures))

  (defbitstruct modr/m
    ((r/m 3bits)
     (reg 3bits)
     (mod 2bits))
    :inline t
    :msb-first nil)

  (defthm return-type-of-ModR/M->r/m-linear
    (< (ModR/M->r/m modr/m) 8)
    :hints (("Goal" :in-theory (e/d (ModR/M->r/m) ())))
    :rule-classes :linear)

  (defthm return-type-of-ModR/M->reg-linear
    (< (ModR/M->reg modr/m) 8)
    :hints (("Goal" :in-theory (e/d (ModR/M->reg) ())))
    :rule-classes :linear)

  (defthm return-type-of-ModR/M->mod-linear
    (< (ModR/M->mod modr/m) 4)
    :hints (("Goal" :in-theory (e/d (ModR/M->mod modr/m-fix) ())))
    :rule-classes :linear))

(defsection SIB-structures

  :parents (SIB-decoding structures)
  :short "Bitstruct definitions to store a SIB byte and its fields"

  (defbitstruct sib
    ((base  3bits)
     (index 3bits)
     (scale 2bits))
    :inline t
    :msb-first nil)

  (defthm return-type-of-sib->base-linear
    (< (sib->base sib) 8)
    :hints (("Goal" :in-theory (e/d (sib->base) ())))
    :rule-classes :linear)

  (defthm return-type-of-sib->index-linear
    (< (sib->index sib) 8)
    :hints (("Goal" :in-theory (e/d (sib->index) ())))
    :rule-classes :linear)

  (defthm return-type-of-sib->scale-linear
    (< (sib->scale sib) 4)
    :hints (("Goal" :in-theory (e/d (sib->scale sib-fix) ())))
    :rule-classes :linear))

;; ----------------------------------------------------------------------

;; Rflags:

(defbitstruct rflagsBits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 1, Section 3.4.3</p>"
  ((cf bitp)      ; carry flag
   (res1 bitp :default '1)    ; 1 (reserved)
   (pf bitp)      ; parity flag
   (res2 bitp :default '0)    ; 0 (reserved)
   (af bitp)      ; auxiliary-carry flag
   (res3 bitp :default '0)    ; 0 (reserved)
   (zf bitp)      ; zero flag
   (sf bitp)      ; sign flag
   (tf bitp)      ; trap flag
   (intf bitp)    ; interrupt-enable flag
   (df bitp)      ; direction flag
   (of bitp)      ; overflow flag
   (iopl 2bits)  ; i/o privilege level
   (nt bitp)      ; nested task
   (res4 bitp :default '0)    ; 0 (reserved)
   (rf bitp)      ; resume flag
   (vm bitp)      ; virtual-8086 mode
   (ac bitp)      ; alignment check
   (vif bitp)     ; virtual interrupt flag
   (vip bitp)     ; virtual interrupt pending
   (id bitp)      ; id flag
   (res5 10bits) ; 0 (reserved)
;   (reserved     32 32) ; reserved bits
   )
  :msb-first nil
  :inline t)

(local
 (defthm rflagsBits-layout-ok
   (iff (rflagsBits-p x)
        (unsigned-byte-p 32 x))
   :rule-classes nil))

;; Enable the following for RoW proofs involving rflags (bitstruct accessor and
;; updater functions):

(def-ruleset rflag-RoWs-enables
  '(!rflagsBits->cf-is-rflagsBits
    !rflagsBits->res1-is-rflagsBits
    !rflagsBits->pf-is-rflagsBits
    !rflagsBits->res2-is-rflagsBits
    !rflagsBits->af-is-rflagsBits
    !rflagsBits->res3-is-rflagsBits
    !rflagsBits->zf-is-rflagsBits
    !rflagsBits->sf-is-rflagsBits
    !rflagsBits->tf-is-rflagsBits
    !rflagsBits->intf-is-rflagsBits
    !rflagsBits->df-is-rflagsBits
    !rflagsBits->of-is-rflagsBits
    !rflagsBits->iopl-is-rflagsBits
    !rflagsBits->nt-is-rflagsBits
    !rflagsBits->res4-is-rflagsBits
    !rflagsBits->rf-is-rflagsBits
    !rflagsBits->vm-is-rflagsBits
    !rflagsBits->ac-is-rflagsBits
    !rflagsBits->vif-is-rflagsBits
    !rflagsBits->vip-is-rflagsBits
    !rflagsBits->id-is-rflagsBits
    !rflagsBits->res5-is-rflagsBits))

;; ----------------------------------------------------------------------

;; Control Registers:

(defbitstruct cr0Bits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5</p>"
  ((pe bitp        "Protection Enable")
   (mp bitp        "Monitor coProcessor")
   (em bitp        "Emulation Bit")
   (ts bitp        "Task Switched")
   (et bitp        "Extension Type")
   (ne bitp        "Numeric Error")
   (res1 10bits "0 (Reserved)")
   (wp bitp        "Write Protect")
   (res2 bitp     "0 (Reserved)")
   (am bitp        "Alignment Mask")
   (res3 10bits  "0 (Reserved)")
   (nw bitp        "Not Write-through")
   (cd bitp        "Cache Disable")
   (pg bitp        "Paging Bit"))
  :msb-first nil
  :inline t)

(local
 (defthm cr0-layout-ok
   (iff (cr0Bits-p x)
        (unsigned-byte-p 32 x))
   :rule-classes nil))

(defbitstruct cr3Bits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5</p>"
  ((res1 3bits)  ;; 0
   (pwt bitp)      ;; Page-Level Writes Tranparent
   (pcd bitp)      ;; Page-Level Cache Disable
   (res2 7bits)  ;; 0
   (pdb 40bits)   ;; Page Directory Base
   (res3 12bits) ;; Reserved (must be zero)
   )
  :msb-first nil
  :inline t)

(local
 (defthm cr3-layout-ok
   (iff (cr3Bits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct cr4Bits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5</p>"
  ((vme bitp)        ;; Virtual-8086 Mode Extensions
   (pvi bitp)        ;; Protected-Mode Virtual Interrupts
   (tsd bitp)        ;; Time-Stamp Disable
   (de bitp)         ;; Debugging Extensions
   (pse bitp)        ;; Page Size Extensions
   (pae bitp)        ;; Physical Address Extension
   (mce bitp)        ;; Machine-Check Enable
   (pge bitp)        ;; Page Global Enable
   (pce bitp)        ;; Performance Monitoring Counter Enable
   (osfxsr bitp)     ;; OS Support for FXSAVE and FXRSTOR
   (osxmmexcpt bitp) ;; OS Support for unmasked SIMD FP Exceptions
   (umip bitp)       ;; User-mode instruction prevention
   (la57 bitp)       ;; enables 5-level paging
   (vmxe bitp)       ;; VMX Enable Bit
   (smxe bitp)       ;; SMX Enable Bit
   (res1 bitp)      ;; 0 (Reserved)
   (fsgsbase bitp)   ;; FSGSBase-Enable Bit (Enables the
   ;; instructions RDFSBASE, RDGSBASE,
   ;; WRFSBASE, and WRGSBASE.)
   (pcide bitp)   ;; PCID-Enable Bit
   (osxsave bitp) ;; XSAVE and Processor Extended States
   ;; Enable Bit
   (res2 bitp) ;; 0 (Reserved)
   (smep bitp)  ;; Supervisor Mode Execution Prevention
   (smap bitp)
   ;;     (:cr4-pke        22  1) ;; Protection Key Enable
   ;; Bit
   ;;  (0               22 42) ;; 0 (Reserved)

   )
  :msb-first nil
  :inline t)

(local
 (defthm cr4-layout-ok
   (iff (cr4Bits-p x)
        (unsigned-byte-p
         ;; 64 --- A smaller value here avoids bignum creation.
         22 x))
   :rule-classes nil))

; Intel manual, Mar'17, Vol. 3A, Section 10.8.6
(defbitstruct cr8Bits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5</p>"
  (
   ;; Task Priority Level (width = 4). This sets
   ;; the threshold value corresponding to the
   ;; highest- priority interrupt to be
   ;; blocked. A value of 0 means all interrupts
   ;; are enabled. This field is available in 64-
   ;; bit mode. A value of 15 means all
   ;; interrupts will be disabled.

   (cr8-trpl 4bits) ;; Task Priority Level
   ;;  (0                4 59) ;; 0 (Reserved)

   )
  :msb-first nil
  :inline t)

(local
 (defthm cr8-layout-ok
   (iff (cr8Bits-p x)
        (unsigned-byte-p ;; 64
         ;; A smaller value here avoids
         ;; bignum creation.
         4
         x))
   :rule-classes nil))

(defbitstruct xcr0Bits
  :long "<p>Source: Intel manual, May'18, Vol. 3A, Figure 2-8</p>"
  ;; Software can access XCR0 only if CR4.OSXSAVE[bit 18] = 1. (This bit
  ;; is also readable as CPUID.01H:ECX.OSXSAVE[bit 27].)

  ((fpu/mmx-state bitp) ;; This bit must be 1.  An attempt
   ;; to write 0 to this bit causes a
   ;; #GP exception.
   (sse-state bitp)
   (avx-state bitp)
   (bndreg-state bitp)
   (bndcsr-state bitp)
   (opmask-state bitp)
   (zmm_hi256-state bitp)
   (hi16_zmm-state bitp)
   (res1 bitp) ;; 0 (Reserved)
   (pkru-state bitp)
   (res2 54bits) ;; 0 (Reserved)
   )
  :msb-first nil
  :inline t)

(local
 (defthm xcr0-layout-ok
   (iff (xcr0Bits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------

;; Model-specific Registers:

;; IA32_EFER (Intel Manual, Feb-14, Vol. 3A, Section 2.2.1):
(defbitstruct ia32_eferBits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.2.1</p>"
  ((sce bitp)    ;; Syscall Enable (R/W) (enables SYSCALL/SYSRET)
   (res1 7bits) ;; Reserved?
   (lme bitp)    ;; Long Mode Enabled (R/W)
   (res2 bitp)   ;; Reserved?
   (lma bitp)    ;; Long Mode Active (R)
   (nxe bitp)    ;; Execute Disable Bit Enable (R/W)
   ;; (Enables page access restriction by
   ;; preventing instruction fetches from
   ;; PAE pages with the XD bit set)
;   (0               12 52) ;; Reserved (must be zero)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32_efer-layout-ok
   (iff (ia32_eferBits-p x)
        (unsigned-byte-p 12 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------
