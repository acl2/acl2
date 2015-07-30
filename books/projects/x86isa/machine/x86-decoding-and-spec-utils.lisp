;; AUTHORS:
;; Shilpi Goel <shigoel@cs.utexas.edu>
;; Matt Kaufmann <kaufmann@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-other-non-det"
              :ttags (:include-raw :undef-flg :syscall-exec :other-non-det))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(in-theory (e/d () (mv-nth)))

;; ======================================================================

(defsection x86-decoding-and-spec-utils
  :parents (machine)
  :short "Misc. utilities for instruction decoding. and for writing
  instruction specification functions" )

;; ======================================================================

(defsection error-objects

  :parents (x86-decoding-and-spec-utils)

  :short "Utilities trafficking in @('erp') objects"

  :long "<p>We introduce several utilities trafficking in @('erp')
objects, each of which is a stack of individual error objects
typically of the form <tt>(ctx . kwd-alist)</tt>, where @('ctx') is
typically a function name.  We do not enforce the shape of an
individual error object, however.</p>

<ul>
<li> @('!ms-erp'): This macro assumes that @('erp') is already bound
to an error stack, and @('ctx') is bound to the current context, which
is typically the function name (a symbol).</li>

<li> @('!ms-erp-fresh'): This is same as @('!ms-erp'), but where
@('erp') is not bound and we bind it to @('nil').  </li>

<li> @('!!ms'): @('erp'), @('ctx'), and also @('x86') must already
be bound.  We return an updated @('x86') that has a non-nil @('ms')
field conveying useful information. </li>

<li>@('!!ms-fresh'): @('ctx') must already be bound.</li>

</ul>

@(def !ms-erp)

@(def !ms-erp-fresh)

@(def !!ms)

@(def !!ms-fresh)"

  (defmacro !ms-erp (&rest args)
    `(cons (list ctx ,@args)
           erp))

  (defmacro !ms-erp-fresh (&rest args)
    `(let ((erp nil))
       (!ms-erp ,@args)))

  (defmacro !!ms (&rest args)
    `(!ms (!ms-erp :rip (rip x86) ,@args)
          x86))

  (defmacro !!ms-fresh (&rest args)
    `(!ms (!ms-erp-fresh :rip (rip x86) ,@args)
          x86))
  )

(define 64-bit-modep (x86)
  (declare (ignore x86))

  :parents (x86-decoding-and-spec-utils)
  :short "@('64-bit-modep') is simply true, since we are focusing only
  on the 64-bit mode for now."
  t)

;; ======================================================================

(defsection effective-address-computations

  :parents (x86-decoding-and-spec-utils)

  :short "Computing effective address using ModR/M, SIB bytes, and
  displacement bytes present in the instruction"

  (local (xdoc::set-default-parents effective-address-computations))

  (define x86-effective-addr-from-sib
    ((temp-rip :type (signed-byte #.*max-linear-address-size*))
     (rex-byte :type (unsigned-byte 8) "REX byte")
     (mod      :type (unsigned-byte 2) "mod field of a ModR/M byte")
     (sib      :type (unsigned-byte 8) "SIB byte")
     x86)

    :short "Calculates effective address when SIB is present."
    :long "<p>Source: Intel Vol. 2A, Table 2-3.</p>"

    :returns (mv flg
                 (non-truncated-memory-address
                  integerp :hyp (and (force (x86p x86))
                                     (integerp temp-rip))
                  :rule-classes :type-prescription)
                 disp
                 (increment-RIP-by natp :rule-classes :type-prescription)
                 (x86 x86p :hyp (force (x86p x86))))

    :prepwork ((local (in-theory (e/d (rim-size) ()))))

    (b* ((b (sib-base sib))
         ((mv flg base displacement nrip-bytes x86)

          (case mod

            (0 (if (equal b 5)
                   (b* (((mv ?flg0 dword x86)
                         (rim-size 4 temp-RIP :x x86)) ;; sign-extended
                        ((when flg0)
                         (mv (cons flg0 'rim-size-error) 0 0 0 x86)))
                       (mv nil 0 dword 4 x86))
                 (mv nil (rgfi (reg-index b rex-byte #.*b*) x86) 0 0 x86)))

            (1 (b* (((mv ?flg1 byte x86)
                     (rim-size 1 temp-RIP :x x86)) ;; sign-extended
                    ((when flg1)
                     (mv (cons flg1 'rim-size-error) 0 0 0 x86)))
                   (mv nil (rgfi (reg-index b rex-byte #.*b*) x86)
                       byte 1 x86)))

            (2 (b* (((mv ?flg2 dword x86)
                     (rim-size 4 temp-RIP :x x86)) ;; sign-extended
                    ((when flg2)
                     (mv (cons flg2 'rim-size-error) 0 0 0 x86)))
                   (mv nil (rgfi (reg-index b rex-byte #.*b*) x86)
                       dword 4 x86)))

            (otherwise ;; can't happen: (< mod 3)
             (mv 'mod-can-not-be-anything-other-than-0-1-or-2 0 0 0 x86))))

         (ix ;; use REX-BYTE prefix (cf. Intel Table 2-5 p. 2-13)
          (reg-index (sib-index sib) rex-byte #.*x*))

         (index (case ix ; Fig. 2-6, p. 2-12
                  (4 0) ; no index register; "none" in Intel Table 2-3
                  (otherwise (rgfi ix x86))))

         (scale (the (unsigned-byte 2) (sib-scale sib)))
         (scaled-index (ash index scale))

         (effective-addr (+ base displacement scaled-index)))

        (mv flg effective-addr 0 nrip-bytes x86))

    ///

    (defthm x86-effective-addr-from-sib-returns-natp-displacement
      (equal (mv-nth 2 (x86-effective-addr-from-sib
                        temp-RIP rex-byte mod sib x86))
             0)
      :hints (("Goal" :in-theory (e/d (rim-size) ()))))

    (defthm x86-effective-addr-from-sib-returns-<=-increment-rip-bytes
      (<= (mv-nth 3 (x86-effective-addr-from-sib temp-RIP rex-byte mod
                                                 sib x86))
          4)
      :hints (("Goal" :in-theory (e/d (rim-size) ())))
      :rule-classes :linear))

  (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm logext-loghead-identity
     (implies (signed-byte-p n x)
              (equal (logext n (loghead n x))
                     x))
     :hints (("Goal" :in-theory (e/d (logext loghead logapp logbitp) ())))))

  (define x86-effective-addr
    (p4
     (temp-RIP       :type (signed-byte   #.*max-linear-address-size*) )
     (rex-byte       :type (unsigned-byte 8) "Rex byte")
     (r/m            :type (unsigned-byte 3) "r/m field of ModR/M byte")
     (mod            :type (unsigned-byte 2) "mod field of ModR/M byte")
     (sib            :type (unsigned-byte 8) "Sib byte")
     ;; num-imm-bytes is needed for computing the next RIP when
     ;; RIP-relative addressing is done.
     (num-imm-bytes  :type (unsigned-byte 3)
                     "Number of immediate bytes (0, 1, 2, or 4) that follow the sib (or displacement bytes, if any).")
     x86)

    :guard-hints (("Goal" :in-theory (e/d (n64-to-i64) ())))

    ;; Returns the flag, the effective address (taking the SIB and
    ;; ModR/M bytes into account) and the number of bytes to increment
    ;; the temp-RIP by.
    :returns (mv
              flg
              i64p-memory-address
              increment-RIP-by
              (x86 x86p :hyp (force (x86p x86))))


    :long "<p> We do not add the FS and GS bases (if FS and GS
    overrides are present) to the effective address computed in this
    function.  We choose do so either directly in the instruction
    semantic functions or in functions like @(see
    x86-operand-from-modr/m-and-sib-bytes) and @(see
    x86-operand-to-reg/mem).</p>

    <p>Quoting from Intel Vol 1, Sec 3.3.7:</p>

       <p><em>In 64-bit mode, the effective address components are
       added and the effective address is truncated (See for example
       the instruction LEA) before adding the full 64-bit segment
       base. The base is never truncated, regardless of addressing
       mode in 64-bit mode.</em></p>

      <p>Quoting Intel Vol. 1 Sec. 3.3.7 (Address Calculations in
      64-Bit Mode) pp. 3-12 to 3-13:</p>

        <p><em>All 16-bit and 32-bit address calculations are
        zero-extended in IA-32e mode to form 64-bit addresses. Address
        calculations are first truncated to the effective address size
        of the current mode (64-bit mode or compatibility mode), as
        overridden by any address-size prefix. The result is then
        zero-extended to the full 64-bit address width. Because of
        this, 16-bit and 32-bit applications running in compatibility
        mode can access only the low 4 GBytes of the 64-bit mode
        effective addresses. Likewise, a 32-bit address generated in
        64-bit mode can access only the low 4 GBytes of the 64-bit
        mode effective addresses.</em></p>

    <p>Also: Intel Vol 1. p3.12, Section 3.3.7 says that we need
    sign-extended displacements in effective address calculations. In
    Lisp, sign-extension is implicit.</p>

    <p>In 64-bit mode, instructions such as LEA use this function to
    compute the effective address.  LEA, at least, does not check
    whether the generated address is canonical or not, which is why we
    don't make the canonical-address-p check in this function.</p>"

    (b* (((mv flg addr displacement increment-RIP-by x86)

          (case mod

            (0
             (case r/m
               (4
                ;; Returns
                ;; (mv flg non-truncated-memory-address 0 increment-RIP-by x86)
                (x86-effective-addr-from-sib temp-RIP rex-byte mod sib
                                             x86))
               (5 ;; RIP-relative addressing
                (if (64-bit-modep x86)
                    (b* (((mv ?flg0 dword x86)
                          ;; dword1 is the sign-extended displacement
                          ;; present in the instruction.
                          (rim-size 4 temp-RIP :x x86))
                         ;; next-rip is the rip of the next instruction.
                         ;; temp-RIP + 4 bytes of the displacement
                         ;; mentioned above + bytes of rest of the
                         ;; instruction (immediate bytes)
                         (next-rip (+ temp-RIP 4 num-imm-bytes)))
                        (mv flg0 next-rip dword 4 x86))
                  (mv 'non-64-bit-modes-unimplemented 0 0 0 x86)))

               (otherwise
                (mv nil (rgfi (reg-index r/m rex-byte #.*b*) x86) 0 0
                    x86))))

            (1
             (case r/m
               (4
                ;; Returns
                ;; (mv flg non-truncated-memory-address 0 increment-RIP-by x86)
                (x86-effective-addr-from-sib temp-RIP rex-byte mod sib
                                             x86))

               (otherwise
                (b* (((mv ?flg2 byte2 x86)
                      (rim-size 1 temp-RIP :x x86)) ; sign-extended
                     (reg (rgfi (reg-index r/m rex-byte #.*b*) x86)))
                    (mv flg2 reg byte2 1 x86)))))

            (2
             (case r/m
               (4
                ;; Returns
                ;; (mv flg non-truncated-memory-address 0 increment-RIP-by x86)
                (x86-effective-addr-from-sib temp-RIP rex-byte mod sib
                                             x86))

               (otherwise
                (b* (((mv ?flg1 dword x86)
                      (rim-size 4 temp-RIP :x x86)) ; sign-extended
                     (reg (rgfi (reg-index r/m rex-byte #.*b*) x86)))
                    (mv flg1 reg dword 4 x86)))))

            (otherwise ; shouldn't happen
             (mv 'mod-value-wrong 0 0 0 x86))))

         (dst-base (+ addr displacement))

         ;; In 64-bit mode, if #x67 (address-override prefix) is
         ;; present, the effective address size is 32 bits, else it is
         ;; 64 bits.  Note that our current virtual memory functions can
         ;; cause an error if the address we are reading from/writing to
         ;; is >= 2^47-8.

         (dst-base (if p4
                       (n32 dst-base)
                     (n64-to-i64 (n64 dst-base)))))

        (mv flg dst-base increment-RIP-by x86))

    ///

    (local (in-theory (e/d () (force (force)))))


    (defthm-sb i64p-mv-nth-1-x86-effective-addr
      :hyp t
      :bound 64
      :concl (mv-nth 1 (x86-effective-addr
                        p4 temp-RIP rex-byte r/m mod sib
                        num-imm-bytes x86))
      :gen-linear t
      :gen-type t)

    (defthm natp-mv-nth-2-x86-effective-addr
      (natp (mv-nth 2 (x86-effective-addr
                       p4 temp-RIP rex-byte r/m mod sib
                       num-imm-bytes x86)))
      :rule-classes :type-prescription)

    (defthm mv-nth-2-x86-effective-addr-<=-4
      (<= (mv-nth 2 (x86-effective-addr
                     p4 temp-RIP rex-byte r/m mod sib
                     num-imm-bytes x86))
          4)
      :rule-classes :linear))

  )

;; ======================================================================

(local
 (defthm-usb usb-80-of-16-and-64
   :hyp (and (unsigned-byte-p 16 n16)
             (unsigned-byte-p 64 n64))
   :bound 80
   :concl (logior n16 (ash n64 16))
   :gen-type t
   :gen-linear t
   :hints-l (("Goal"
              :do-not '(preprocess)
              :in-theory (e/d () (unsigned-byte-p))))))

(local
 (defthm-usb usb-48-of-16-and-32
   :hyp (and (unsigned-byte-p 16 n16)
             (unsigned-byte-p 32 n32))
   :bound 48
   :concl (logior n16 (ash n32 16))
   :gen-type t
   :gen-linear t
   :hints-l (("Goal"
              :do-not '(preprocess)
              :in-theory (e/d () (unsigned-byte-p))))))

(defsection read-operands-and-write-results

  :parents (x86-decoding-and-spec-utils)

  :short "Functions to fetch and read operands from an instruction,
  and to write results to appropriate registers/memory locations,
  based on ModR/M, SIB, immediate, and/or displacement bytes."

  (local (xdoc::set-default-parents read-operands-and-write-results))

  (define x86-operand-from-modr/m-and-sib-bytes

    ((reg-type      :type (unsigned-byte  1) "@('reg-type') is @('*rgf-access*') for GPRs, and @('*xmm-access*') for XMMs.")
     (operand-size  :type (member 1 2 4 6 8 10 16))
     (p2            :type (unsigned-byte  8) "Segment Override Prefix")
     (p4?           :type (or t nil)         "Address-Size Override Prefix Present?")
     (temp-rip      :type (signed-byte   #.*max-linear-address-size*))
     (rex-byte      :type (unsigned-byte 8))
     (r/m           :type (unsigned-byte 3))
     (mod           :type (unsigned-byte 2))
     (sib           :type (unsigned-byte 8))
     (num-imm-bytes :type (unsigned-byte 3))
     x86)

    :guard (if (equal mod #b11)
               (cond
                ((equal reg-type #.*rgf-access*)
                 (member operand-size '(1 2 4 8)))
                (t (member operand-size '(4 8 16))))
             (member operand-size '(member 1 2 4 6 8 10 16)))

    :returns
    (mv flg
        operand
        increment-RIP-by
        v-addr
        (x86 x86p :hyp (force (x86p x86))))

    (b* (((mv ?flg0 (the (signed-byte 64) v-addr0) (the (integer 0 4) increment-RIP-by) x86)
          (if (equal mod #b11)
              (mv nil 0 0 x86)
            (x86-effective-addr p4? temp-rip rex-byte r/m mod sib num-imm-bytes x86)))
         ((when flg0)
          (mv (cons 'x86-effective-addr-error flg0) 0 0 0 x86))

         ;; Since msri returns an n64p, we will convert it into an
         ;; i64p.  Moreover, FS and GS base addresses should always be
         ;; canonical.  Actually, if the values written to the FS and
         ;; GS base addresses aren't canonical, a #GP exception is
         ;; raised.  However, I'll do a canonical-address-p check on
         ;; FS and GS base here anyway.

         ;; Quoting from Intel Vol. 3, Section 3.4.4:

         ;; "The hidden descriptor register fields for FS.base and
         ;; GS.base are physically mapped to MSRs in order to load all
         ;; address bits supported by a 64-bit
         ;; implementation. Software with CPL = 0 (privileged
         ;; software) can load all supported linear-address bits into
         ;; FS.base or GS.base using WRMSR. Addresses written into the
         ;; 64-bit FS.base and GS.base registers must be in canonical
         ;; form. A WRMSR instruction that attempts to write a
         ;; non-canonical address to those registers causes a #GP
         ;; fault."


         ((mv flg1 v-addr)
          (if (equal mod #b11)
              (mv nil 0)
            (case p2
              ;; p2 is 0 when there is no segment override prefix
              ;; present. This first case below saves unnecessary
              ;; comparisons with *fs-override* and *gs-override* in
              ;; that case.
              (0 (mv nil v-addr0))
              (#.*fs-override*
               (let* ((nat-fs-base (msri *IA32_FS_BASE-IDX* x86))
                      (fs-base (n64-to-i64 nat-fs-base)))
                 (if (not (canonical-address-p fs-base))
                     (mv 'Non-Canonical-FS-Base fs-base)
                   (mv nil (+ fs-base v-addr0)))))
              (#.*gs-override*
               (let* ((nat-gs-base (msri *IA32_GS_BASE-IDX* x86))
                      (gs-base (n64-to-i64 nat-gs-base)))
                 (if (not (canonical-address-p gs-base))
                     (mv 'Non-Canonical-GS-Base gs-base)
                   (mv nil (+ gs-base v-addr0)))))
              (t
               ;; All other segments are considered to have base address
               ;; = 0 in 64-bit mode.
               (mv nil v-addr0)))))
         ((when flg1)
          (mv (cons 'Segment-Override-Error flg1) 0 0 0 x86))

         ((when (and (not (equal mod #b11))
                     (not (canonical-address-p v-addr))))
          (mv 'x86-operand-from-modr/m-and-sib-bytes-Non-Canonical-Address-Encountered
              0 0 0 x86))

         ((mv ?flg2 operand x86)
          (if (equal mod #b11)
              (if (int= reg-type #.*rgf-access*)
                  (mv nil (rgfi-size operand-size (reg-index r/m rex-byte #.*b*)
                                     rex-byte x86) x86)
                (mv nil (xmmi-size operand-size (reg-index r/m rex-byte #.*b*)
                                   x86) x86))
            (rm-size operand-size v-addr :x x86)))
         ((when flg2)
          (mv (cons 'Rm-Size-Error flg2) 0 0 0 x86)))

        (mv nil operand increment-RIP-by v-addr x86))

    ///

    (defthm-usb bound-of-mv-nth-1-x86-operand-from-modr/m-and-sib-bytes-operand
      :hyp (and (member operand-size '(1 2 4 8 16))
                (equal bound (ash operand-size 3))
                (x86p x86))
      :bound bound
      :concl (mv-nth 1 (x86-operand-from-modr/m-and-sib-bytes
                        reg-type operand-size p2 p4? temp-RIP rex-byte r/m mod sib
                        num-imm-bytes x86))
      :gen-linear t
      :gen-type t)

    (defthm-usb bound-of-mv-nth-1-x86-operand-from-modr/m-and-sib-bytes-operand-6-and-10-bytes-read
      :hyp (and (member operand-size '(6 10))
                (equal bound (ash operand-size 3))
                (not (equal mod #b11))
                (x86p x86))
      :bound bound
      :concl (mv-nth 1 (x86-operand-from-modr/m-and-sib-bytes
                        reg-type operand-size p2 p4? temp-RIP rex-byte r/m mod sib
                        num-imm-bytes x86))
      :gen-linear t
      :gen-type t)

    (defthm integerp-x86-operand-from-modr/m-and-sib-bytes-increment-RIP-by-type-prescription
      (implies (force (x86p x86))
               (natp (mv-nth 2 (x86-operand-from-modr/m-and-sib-bytes
                                reg-type operand-size p2 p4 temp-RIP rex-byte r/m mod sib
                                num-imm-bytes x86))))
      :hints (("Goal" :in-theory (e/d (rm-size) ())))
      :rule-classes :type-prescription)

    (defthm mv-nth-2-x86-operand-from-modr/m-and-sib-bytes-increment-RIP-by-linear<=4
      (implies (x86p x86)
               (<= (mv-nth 2 (x86-operand-from-modr/m-and-sib-bytes
                              reg-type operand-size p2 p4 temp-RIP rex-byte r/m mod sib
                              num-imm-bytes x86))
                   4))
      :hints (("Goal" :in-theory (e/d (rm-size) ())))
      :rule-classes :linear)

    (defthm-sb i48p-x86-operand-from-modr/m-and-sib-bytes
      :hyp (forced-and (x86p x86))
      :bound 48
      :concl (mv-nth 3 (x86-operand-from-modr/m-and-sib-bytes
                        reg-type operand-size p2 p4 temp-rip rex-byte r/m mod sib
                        num-imm-bytes x86))
      :gen-linear t
      :gen-type t)

    (defthm canonical-address-p-x86-operand-from-modr/m-and-sib-bytes-v-addr
      (implies (forced-and (x86p x86))
               (canonical-address-p
                (mv-nth 3 (x86-operand-from-modr/m-and-sib-bytes
                           reg-type operand-size p2 p4 temp-rip rex-byte r/m mod sib
                           num-imm-bytes x86))))))

  (define x86-operand-to-reg/mem

    ((operand-size :type (member 1 2 4 6 8 10 16))
     (operand      :type (integer 0 *))
     (v-addr       :type (signed-byte #.*max-linear-address-size*))
     (rex-byte     :type (unsigned-byte 8))
     (r/m          :type (unsigned-byte 3))
     (mod          :type (unsigned-byte 2))
     x86)

    :long "<p> The reason why the type of v-addr here is i64p instead
    of i49p is that the v-addr might be obtained from a 64-bit
    register or be a 64-bit value in the memory.  Also note that this
    v-addr includes the FS or GS-base if the appropriate prefix
    overrides are present.</p>"

    :guard (and (unsigned-byte-p (ash operand-size 3) operand)
                (if (equal mod #b11)
                    (member operand-size '(member 1 2 4 8))
                  (member operand-size '(member 1 2 4 6 8 10 16))))

    (b* (((when (equal mod #b11))
          (let* ((x86 (!rgfi-size operand-size (reg-index r/m rex-byte #.*b*)
                                  operand rex-byte x86)))
            (mv nil x86)))

         ((mv flg x86)
          (wm-size operand-size v-addr operand x86)))
        (mv flg x86))

    ///

    (defthm x86p-x86-operand-to-reg/mem
      (implies (force (x86p x86))
               (x86p (mv-nth 1 (x86-operand-to-reg/mem operand-size
                                                       operand v-addr
                                                       rex-byte r/m mod
                                                       x86))))
      :hints (("Goal" :in-theory (e/d () (force (force)))))))

  (define x86-operand-to-xmm/mem

    ((operand-size :type (member 4 8 16))
     (operand      :type (integer 0 *))
     (v-addr       :type (signed-byte #.*max-linear-address-size*))
     (rex-byte     :type (unsigned-byte 8))
     (r/m          :type (unsigned-byte 3))
     (mod          :type (unsigned-byte 2))
     x86)

    :long "<p> The reason why the type of v-addr here is i64p instead
    of i49p is that the v-addr might be obtained from a 64-bit
    register or be a 64-bit value in the memory.  Also note that this
    v-addr includes the FS or GS-base if the appropriate prefix
    overrides are present.</p>"

    :guard (unsigned-byte-p (ash operand-size 3) operand)

    (b* (((when (equal mod #b11))
          (let* ((x86 (!xmmi-size operand-size (reg-index r/m rex-byte #.*b*)
                                  operand x86)))
            (mv nil x86)))

         ((mv flg x86)
          (wm-size operand-size v-addr operand x86)))
        (mv flg x86))

    ///

    (defthm x86p-x86-operand-to-xmm/mem
      (implies (force (x86p x86))
               (x86p (mv-nth 1 (x86-operand-to-xmm/mem operand-size
                                                       operand v-addr
                                                       rex-byte r/m mod
                                                       x86))))
      :hints (("Goal" :in-theory (e/d () (force (force))))))))

;; ======================================================================

;; Some misc. stuff to be used to define instruction semantic
;; functions:

;; implemented-opcodes-table contains information about opcodes that
;; are supported by the model.  We build the information in the table
;; when defining instruction semantic functions using the macro
;; def-inst.

;; ----------------------------------------------------------------------

(program)

(defun add-to-implemented-opcodes-table-fn
  (opcode-name opcode type fn-name world state)
  (declare (xargs :stobjs state
                  :guard (and (natp opcode)
                              (true-listp type)
                              (symbolp fn-name))))
  (if (function-symbolp fn-name world)
      (value `(table implemented-opcodes-table
                     (cons ',opcode ',type)
                     (cons ',opcode-name ',fn-name)))
    (er soft 'add-to-implemented-opcodes-table
        "Semantic function ~x0 is invalid!~%" fn-name)))

(defmacro add-to-implemented-opcodes-table
  (opcode-name opcode type fn-name)
  `(make-event
    (add-to-implemented-opcodes-table-fn
     ,opcode-name ,opcode ,type ,fn-name (w state) state)))

(logic)

;; ----------------------------------------------------------------------

(defmacro def-inst
  (name &key (operation 'nil)
        (sp/dp 'nil)
        ;; Will raise an error as a part of calling
        ;; add-to-implemented-opcodes-table when def-inst is expanded
        ;; and "implemented" is not an embedded event form.
        (implemented 't)
        body parents short long
        inline enabled guard-debug guard
        guard-hints (verify-guards 't) prepwork thms
        returns)

  (if body
      `(define ,name
         (,@(and operation `((operation :type (integer 0 8))))
          ,@(and sp/dp     `((sp/dp     :type (integer 0 1))))
          (start-rip :type (signed-byte   #.*max-linear-address-size*))
          (temp-rip  :type (signed-byte   #.*max-linear-address-size*))
          (prefixes  :type (unsigned-byte 43))
          (rex-byte  :type (unsigned-byte 8))
          (opcode    :type (unsigned-byte 8))
          (modr/m    :type (unsigned-byte 8))
          (sib       :type (unsigned-byte 8))
          x86
          ;; If operation = -1, ignore this field.  Note that -1 is
          ;; the default value of operation.
          ;; &optional ((operation :type (integer -1 8)) '-1 )
          )

         (declare (ignorable start-rip temp-rip prefixes rex-byte opcode modr/m sib))

         ,@(and parents `(:parents ,parents))
         ,@(and short `(:short ,short))
         ,@(and long `(:long ,long))

         ,@(and prepwork `(:prepwork ,prepwork))

         ,@(and enabled `(:enabled ,enabled))
         ,@(and inline `(:inline ,inline))
         ,@(and guard `(:guard ,guard))
         ,@(and (not verify-guards) `(:verify-guards ,verify-guards))
         ,@(and guard-debug `(:guard-debug ,guard-debug))
         ,@(and guard-hints `(:guard-hints ,guard-hints))

         ,@(and returns `(:returns ,returns))

         ,body

         ///

         (add-to-ruleset instruction-decoding-and-spec-rules
                         '(,name))

         ,implemented

         ,@(and thms
                `(,@thms)))

    nil))


(define select-operand-size
  ((byte-operand? :type (or t nil))
   (rex-byte      :type (unsigned-byte  8))
   (imm?          :type (or t nil))
   (prefixes      :type (unsigned-byte 43)))

  :inline t
  :parents (x86-decoding-and-spec-utils)

  :short "Selecting the operand size for general-purpose instructions"

  :long "<p>@('select-operand-size') selects the operand size of the
  instruction.  It is cognizant of the instruction prefixes, the
  @('rex') byte, the operand type (e.g., immediate operand or not),
  and the default operand size.  Note that this function has been
  written only for the 64-bit mode.</p>

<p>This function was written by referring to the following:
<ol>
<li>Intel Manuals, Vol. 1, Section 3.6, Table 3-4</li>
<li>Intel Manuals, Vol. 2, Section 2.2.1.2</li>
</ol>
</p>

<p><img src='res/x86-images/Vol-1-Table-3-4-small.png' width='8%'
height='8%' />

The image above has been captured from Volume 1: Basic Architecture,
Intel\(R\) 64 and IA-32 Architectures Software Developer's Manual,
Combined Volumes: 1, 2A, 2B, 2C, 3A, 3B and 3C, Order Number:
325462-054US, April 2015.</p>

<i>
<ul>
<li>Setting REX.W can be used to determine the operand size but does
not solely determine operand width. Like the 66H size prefix, 64-bit
operand size override has no effect on byte-specific operations.</li>

<li>For non-byte operations: if a 66H prefix is used with prefix
\(REX.W = 1\), 66H is ignored.</li>

<li>If a 66H override is used with REX and REX.W = 0, the operand size
is 16 bits.</li>
</ul>
</i>"

  :enabled t
  :returns (size natp :rule-classes :type-prescription)

  (if byte-operand?
      1
    (if (logbitp #.*w* rex-byte)
        (if imm?
            ;; Fetch 4 bytes (sign-extended to 64 bits) if operand is
            ;; immediate.
            4
          8)
      (if (eql #.*operand-size-override*
               (prefixes-slice :group-3-prefix prefixes))
          2 ;; 16-bit operand-size
        4   ;; Default 32-bit operand size (in 64-bit mode)
        ))))

;; ======================================================================
