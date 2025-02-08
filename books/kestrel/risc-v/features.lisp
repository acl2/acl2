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
     there is a choice of base (RV32I, RV64I, RV32E, RV64E),
     and there are choices of extensions.
     There is also a choice of little vs. big endian memory access
     (for data; instruction access is always little endian [ISA:1.5.1]).
     Perhaps less obvious, there is also a choice of
     which parts of the address space are readable and/or writable.")
   (xdoc::p
    "For a general model of the RISC-V ISA,
     we want to accommodate all the possible choices.
     Towards that goal, we introduce a notion of `features',
     which define these choices;
     we start with only some choices,
     but we plan to extend it with more choices."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum feat-bits
  :short "Fixtype of RISC-V feature choices for 32 vs. 64 bits."
  :long
  (xdoc::topstring
   (xdoc::p
    "A major feature choice in the RISC-V ISA is
     the choice between 32 and 64 bits."))
  (:32 ())
  (:64 ())
  :pred feat-bitsp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod feat
  :short "Fixtype of RISC-V feature choices."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model the following choices:")
   (xdoc::ul
    (xdoc::li
     "32 vs. 64 bits."))
   (xdoc::p
    "More features will be added later."))
  ((bits feat-bits))
  :pred featp)
