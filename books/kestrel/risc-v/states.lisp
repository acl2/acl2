; RISC-V Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "features")
(include-book "states32")
(include-book "states64")

(include-book "kestrel/utilities/unsigned-byte-fixing" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states
  :parents (riscv)
  :short "Model of states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have two similar but slightly different models,
     one for RV32I and one for RV64I.
     We plan to consolidate them into one model for both;
     towards that end, we also provide a more generic definition here."))
  :default-parent t
  :order-subtopics (states32
                    states64
                    t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stat
  :short "Fixtype of machine states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures all possible states for all possible @(see features).
     Restrictions based on features are formalized in @(see stat-validp).")
   (xdoc::p
    "The processor state always includes the @('x<i>') registers,
     whose number and size depends on the choice of base.
     The size in bits is @('XLEN') [ISA:1.3],
     which is 32 in RV32I/RV32E, or 64 in RV64I/RV64E;
     it is 128 in the upcoming RV128I [ISA:5].
     The number of registers is 32 or 16,
     based on whether the base is RV32I/RV64I or RV32R/RV64E.
     In @(tsee stat-validp),
     we constrain this state component to be
     a list of appropriate type and appropriate length;
     thus, here we do not need to constrain it at all.")
   (xdoc::p
    "The program counter @('pc') has the same size @('XLEN')
     as the @('x') registers.
     In @(tsee stat-validp),
     we constrain this state component to be
     an integer in the appropriate range;
     thus, here we do not need to constrain it at all.")
   (xdoc::p
    "The memory component models the whole addressable space,
     which consists of @('2^XLEN') bytes [ISA:1.4].
     We generically define it as a list of bytes here;
     in @(tsee stat-validp), we constrain its length.")
   (xdoc::p
    "RISC-V extensions may require the extension of this fixtype,
     with more components that support those extensions.
     We will do that as we model those extensions,
     which also requires extending the @(see features).")
   (xdoc::p
    "We also include a boolean flag that says whether an error has occurred.
     This does not exist in the real machine;
     it is just a modeling convenience.
     We may refine this boolean flag into some richer data type."))
  ((xregs)
   (pc)
   (memory ubyte8-list)
   (error bool))
  :pred statp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-validp ((stat statp) (feat featp))
  :returns (yes/no booleanp)
  :short "Check if a state is valid with respect to given features."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee stat),
     that fixtype models all possible machine states for all possible features.
     Here we define restrictions based on features.")
   (xdoc::p
    "For now, the only features we model are
     whether the base is RV32I or RV64I.
     This dictates the size @('XLEN') of the registers, either 32 or 64 bits;
     so we use contrain them to form a list of 32-bit or 64-bit unsigned values.
     The number of registers is @(tsee feat->xnum).
     However, since @('x0') is hardwired to 0 [ISA:2.1],
     we do not model that register explicitly:
     we only model @('x1'), @('x2'), etc.;
     so we constrain the length of the list to be
     one less than the number of registers.")
   (xdoc::p
    "Based on @('XLEN'), we constrain the program counter
     to be either 32 or 64 bits.")
   (xdoc::p
    "The size of the memory is @('2^XLEN'),
     so we constrain the length of the list to be that."))
  (b* (((stat stat) stat)
       (xlen (feat->xlen feat))
       (xnum (feat->xnum feat)))
    (and (unsigned-byte-listp xlen stat.xregs)
         (equal (len stat.xregs) xnum)
         (unsigned-byte-p xlen stat.pc)
         (equal (len stat.memory) (expt 2 xlen))))
  :hooks (:fix)

  ///

  (defrule unsigned-byte-listp-of-stat->xregs
    (implies (stat-validp stat feat)
             (unsigned-byte-listp (feat->xlen feat)
                                  (stat->xregs stat))))

  (defrule true-listp-of-stat->xregs
    (implies (stat-validp stat feat)
             (true-listp (stat->xregs stat)))
    :rule-classes :type-prescription)

  (defrule ubyte32-listp-of-stat->xregs
    (implies (and (stat-validp stat feat)
                  (feat-bits-case (feat->bits feat) :32))
             (ubyte32-listp (stat->xregs stat)))
    :hints
    (("Goal"
      :in-theory (enable acl2::ubyte32-listp-rewrite-unsigned-byte-listp))))

  (defrule ubyte64-listp-of-stat->xregs
    (implies (and (stat-validp stat feat)
                  (feat-bits-case (feat->bits feat) :64))
             (ubyte64-listp (stat->xregs stat)))
    :hints
    (("Goal"
      :in-theory (enable acl2::ubyte64-listp-rewrite-unsigned-byte-listp))))

  (defrule len-of-stat->xregs
    (implies (stat-validp stat feat)
             (equal (len (stat->xregs stat))
                    (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable feat->xnum))))

  (defrule unsigned-byte-p-of-stat->pc
    (implies (stat-validp stat feat)
             (unsigned-byte-p (feat->xlen feat)
                              (stat->pc stat))))

  (defrule ubyte32p-of-stat->pc
    (implies (and (stat-validp stat feat)
                  (feat-bits-case (feat->bits feat) :32))
             (ubyte32p (stat->pc stat)))
    :hints (("Goal" :in-theory (enable ubyte32p))))

  (defrule ubyte64p-of-stat->pc
    (implies (and (stat-validp stat feat)
                  (feat-bits-case (feat->bits feat) :64))
             (ubyte64p (stat->pc stat)))
    :hints (("Goal" :in-theory (enable ubyte64p))))

  (defrule len-of-stat->memory
    (implies (stat-validp stat feat)
             (equal (len (stat->memory stat))
                    (expt 2 (feat->xlen feat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-unsigned ((reg natp) (stat statp) (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (val (unsigned-byte-p (feat->xlen feat) val)
                :hints (("Goal" :in-theory (enable feat->xlen))))
  :short "Read an unsigned integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The index must be less than the number @('n') of registers,
     so that the registers @('x0') to @('x<n>') can be indexed.
     The result is a natural number in general;
     additionally, based on @('XLEN'), it consists of either 32 or 64 bits.")
   (xdoc::p
    "As explained in @(tsee stat),
     @('x0') is not modeled explicitly, since it is hardwired to 0.
     Thus, the 0 index is treated separately;
     the other cases are handled by decrementing the index by 1."))
  (b* ((reg (lnfix reg)))
    (if (= reg 0)
        0
      (acl2::unsigned-byte-fix (feat->xlen feat)
                               (nth (1- reg) (stat->xregs stat)))))
  :hooks (:fix)

  ///

  (defret ubyte32p-of-read-xreg-unsigned
    (ubyte32p val)
    :hyp (and (stat-validp stat feat)
              (feat-bits-case (feat->bits feat) :32)
              (< (lnfix reg) (feat->xnum feat))))

  (defret ubyte64p-of-read-xreg-unsigned
    (ubyte64p val)
    :hyp (and (stat-validp stat feat)
              (feat-bits-case (feat->bits feat) :64)
              (< (lnfix reg) (feat->xnum feat)))))
