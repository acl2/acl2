;; AUTHOR:
;; Alessandro Coglio <coglio@kestrel.edu>

(in-package "X86ISA")

(include-book "register-readers-and-writers" :ttags (:undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

;; ======================================================================

(defxdoc x86-modes
  :parents (machine)
  :short "Modes of operation of the processor."
  :long
  "<p>
   For now we do not model in detail all the processor modes and transitions
   (see Figure 2-3 in Intel Volume 3A).
   We implicitly assume that the processor
   is always in one of the following modes:
   </p>
   <ul>
     <li>Protected mode.</li>
     <li>Compatibility mode (sub-mode of IA-32e mode).</li>
     <li>64-bit mode (sub-mode of IA-32e mode).</li>
   </ul>
   <p>
   No real-address mode, virtual-8086 mode, or system management mode for now.
   </p>")

(define 64-bit-modep (x86)
  :parents (x86-modes)
  :short "Check whether we are in 64-bit mode."
  :long
  "<p>
   Given the above modeling assumption stated in @(see x86-modes),
   this predicate discriminates between
   64-bit mode and the other two modes (collectively, 32-bit mode).
   Based on Intel manual, Mar'17, Vol. 3A, Sec. 2.2 (near Fig. 2-3),
   the discrimination is based on the IA32_EFER.LME and CS.L bits:
   if they are both 1, we are in 64-bit mode,
   otherwise we are in 32-bit mode
   (protected mode if IA32_EFER.LME is 0,
   compatibility mode if IA32_EFER.LME is 1 and CS.L is 0;
   note that when IA32_EFER.LME is 0, CS.L should be 0,
   according to Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5).
   </p>
   <p>
   This predicate does not include state invariants such as
   the constraints imposed by the 64-bit mode consistency checks
   described in Intel manual, Mar'17, Vol. 3A, Sec. 9.8.5.
   </p>
   <p>
   This predicate is useful as a hypothesis of theorems
   about either 64-bit or 32-bit mode.
   </p>
   <p>
   Since @('(xr :msr ... x86)') returns a 64-bit value
   but the IA32_EFER register consists of 12 bits.
   So we use @(tsee n12) to make @('ia32_efer-slice') applicable.
   </p>"
  (b* ((ia32_efer (n12 (xr :msr *ia32_efer-idx* x86)))
       (ia32_efer.lma (ia32_efer-slice :ia32_efer-lma ia32_efer))
       (cs-hidden (xr :seg-hidden *cs* x86))
       (cs-attr (hidden-seg-reg-layout-slice :attr cs-hidden))
       (cs.l (code-segment-descriptor-attributes-layout-slice :l cs-attr)))
    (and (equal ia32_efer.lma 1)
         (equal cs.l 1)))
  ///

  (defrule 64-bit-modep-of-xw ; contributed by Eric Smith
    (implies (and (not (equal fld :msr))
                  (not (equal fld :seg-hidden)))
             (equal (64-bit-modep (xw fld index value x86))
                    (64-bit-modep x86))))

  (defrule 64-bit-modep-of-!flgi ; contributed by Eric Smith
    (equal (64-bit-modep (!flgi flag val x86))
           (64-bit-modep x86)))

  (defrule 64-bit-modep-of-!flgi-undefined
    (equal (64-bit-modep (!flgi-undefined flg x86))
           (64-bit-modep x86))
    :enable !flgi-undefined)

  (defrule 64-bit-modep-of-write-user-rflags
    (equal (64-bit-modep (write-user-rflags vector mask x86))
           (64-bit-modep x86))))
