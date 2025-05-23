; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ features
  :parents (riscv)
  :short "RISC-V features."
  :long
  (xdoc::topstring
   (xdoc::p
    "The RISC-V ISA is really a family of ISAs:
     there is a choice of base (RV32I, RV64I, RV128I, RV32E, RV64E),
     and there are choices of extensions.
     There is also a choice of little or big endian memory access
     (for data; instruction access is always little endian [ISA:1.5.1]).
     Perhaps less obvious, there is also a choice of
     which parts of the address space are readable and/or writable.")
   (xdoc::p
    "For a general model of the RISC-V ISA,
     we want to accommodate all the possible choices.
     Towards that goal, we introduce a notion of `features',
     which define these choices;
     we start with only some choices,
     which we plan to extend with more choices."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum feat-bits
  :short "Fixtype of RISC-V feature choices for 32 or 64 bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "A major feature choice in the RISC-V ISA is
     the choice between 32 and 64 bits.
     The former corresponds to the RV32I and RV32E bases;
     the latter corresponds to the RV64I and RV64E bases.
     For now we do not cover the 128-bit option for the RV128I base [ISA:5];
     note that this part of the RISC-V specification is not frozen yet."))
  (:32 ())
  (:64 ())
  :pred feat-bitsp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod feat
  :short "Fixtype of RISC-V feature choices."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model the following choices:")
   (xdoc::ul
    (xdoc::li
     "32 or 64 bits."))
   (xdoc::p
    "More features will be added later."))
  ((bits feat-bits))
  :pred featp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-32p ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate 32 bits."
  (feat-bits-case (feat->bits feat) :32)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-64p ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate 64 bits."
  (feat-bits-case (feat->bits feat) :64)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat->xlen ((feat featp))
  :returns (xlen posp :rule-classes (:rewrite :type-prescription))
  :short "The @('XLEN') parameter [ISA:1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the register width, depending on the choice of base."))
  (b* (((feat feat) feat))
    (feat-bits-case feat.bits
                    :32 32
                    :64 64))
  :hooks (:fix)

  ///

  (defret feat->xlen-when-32-bits
    (equal xlen 32)
    :hyp (feat-32p feat)
    :hints (("Goal" :in-theory (enable feat-32p))))

  (defret feat->xlen-when-64-bits
    (equal xlen 64)
    :hyp (feat-64p feat)
    :hints (("Goal" :in-theory (enable feat-64p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat->xnum ((feat featp))
  :returns (xnum posp)
  :short "The number of @('x') registers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 32 for the RV32I and RV64I bases,
     but it is reduced to 16 for the RV32E and RV64E bases [ISA:3].
     Although our features do not yet model the latter bases,
     we define this operation so that other code can use it
     and more easily accommodate the extension for RV32E/RV64E."))
  (declare (ignore feat))
  32
  :hooks (:fix))
