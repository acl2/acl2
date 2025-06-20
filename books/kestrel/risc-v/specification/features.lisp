; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
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
  :parents (specification)
  :short "RISC-V features."
  :long
  (xdoc::topstring
   (xdoc::p
    "The RISC-V ISA is really a family of ISAs:
     there is a choice of base (RV32I, RV64I, RV128I, RV32E, RV64E),
     and there are choices of extensions.
     There is also a choice of little or big endian memory access
     (for data; instruction access is always little endian [ISA:1.5]).
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

(fty::deftagsum feat-base
  :short "Fixtype of RISC-V feature choices for the base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We support all the bases:
     RV32I [ISA:2], RV64I [ISA:4], RV32E [ISA:3], and RV64E [ISA:3]."))
  (:rv32i ())
  (:rv64i ())
  (:rv32e ())
  (:rv64e ())
  :pred feat-basep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum feat-endian
  :short "Fixtype of RISC-V feature choices for endianness."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although instruction encodings are always in little endian [ISA:1.5],
     data loaded/stored from/to memory may be little or big endian [ISA:2.6].
     This choice is ``byte-address invariant'' [ISA:2.6],
     i.e. it does not depend on the address;
     so there is just one choice for the whole memory."))
  (:little ())
  (:big ())
  :pred feat-endianp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod feat
  :short "Fixtype of RISC-V feature choices."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model the following choices:")
   (xdoc::ul
    (xdoc::li
     "The base.")
    (xdoc::li
     "The endianness.")
    (xdoc::li
     "Whether the M extension [ISA:12] is present or not."))
   (xdoc::p
    "More features will be added later."))
  ((base feat-base)
   (endian feat-endian)
   (m bool))
  :pred featp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-32p ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate 32 bits."
  (or (feat-base-case (feat->base feat) :rv32i)
      (feat-base-case (feat->base feat) :rv32e))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-64p ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate 64 bits."
  (or (feat-base-case (feat->base feat) :rv64i)
      (feat-base-case (feat->base feat) :rv64e))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled feat-32p-or-64p
  :parents (feat-32p feat-64p)
  :short "One of @(tsee feat-32p) and @(tsee feat-64p) always holds."
  (or (feat-32p feat)
      (feat-64p feat))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((feat-32p feat)
                                                    (feat-64p feat))))
  :enable (feat-32p feat-64p))

(in-theory (enable (:forward-chaining feat-32p-or-64p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule not-feat-32p-and-feat-64p
  :parents (feat-32p feat-64p)
  :short "Both of @(tsee feat-32p) and @(tsee feat-64p) cannot hold."
  (or (not (feat-32p feat))
      (not (feat-64p feat)))
  :rule-classes ((:forward-chaining :trigger-terms ((feat-32p feat)
                                                    (feat-64p feat))))
  :enable (feat-32p feat-64p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-embedp ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate embedded systems."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if the base is RV32E or RV64E."))
  (or (feat-base-case (feat->base feat) :rv32e)
      (feat-base-case (feat->base feat) :rv64e))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-little-endianp ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate little endian."
  (feat-endian-case (feat->endian feat) :little)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-big-endianp ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate bit endian."
  (feat-endian-case (feat->endian feat) :big)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled feat-little-or-big-endianp
  :parents (feat-little-endianp feat-big-endianp)
  :short "One of @(tsee feat-little-endianp) and @(tsee feat-big-endianp)
          always holds."
  (or (feat-little-endianp feat)
      (feat-big-endianp feat))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((feat-little-endianp feat)
                                                    (feat-big-endianp feat))))
  :enable (feat-little-endianp feat-big-endianp))

(in-theory (enable (:forward-chaining feat-little-or-big-endianp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-mp ((feat featp))
  :returns (yes/no booleanp)
  :short "Check if the features indicate the M extension."
  (feat->m feat)
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
    (feat-base-case feat.base
                    :rv32i 32
                    :rv64i 64
                    :rv32e 32
                    :rv64e 64))
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
     but it is reduced to 16 for the RV32E and RV64E bases [ISA:3]."))
  (b* (((feat feat) feat))
    (feat-base-case feat.base
                    :rv32i 32
                    :rv64i 32
                    :rv32e 16
                    :rv64e 16))
  :hooks (:fix)

  ///

  (defret feat->xnum-when-embedp
    (equal xnum 16)
    :hyp (feat-embedp feat)
    :hints (("Goal" :in-theory (enable feat-embedp))))

  (defret feat->xnum-when-not-embedp
    (equal xnum 32)
    :hyp (not (feat-embedp feat))
    :hints (("Goal" :in-theory (enable feat-embedp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat->ialign ((feat featp))
  :returns (ialign posp)
  :short "The @('IALIGN') parameter [ISA:1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently always 32,
     because we do not support the C extension [ISA:27] yet.
     Once we add support for the C extension,
     this will be 16 when the C extension is active in the features.")
   (xdoc::p
    "In any case, @('IALIGN') always consists of
     a whole number of bytes."))
  (declare (ignore feat))
  32
  :type-prescription (and (posp (feat->ialign feat))
                          (> (feat->ialign feat) 1))
  :hooks (:fix)

  ///

  (in-theory (disable (:e feat->ialign)))

  (defret feat->ialign-is-whole-bytes
    (integerp (/ ialign 8))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat->ilen ((feat featp))
  :returns (ilen posp)
  :short "The @('ILEN') parameter [ISA:1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently always 32,
     but it could be larger if we add support for more features."))
  (declare (ignore feat))
  32
  :type-prescription (and (posp (feat->ilen feat))
                          (> (feat->ilen feat) 1))
  :hooks (:fix)

  ///

  (in-theory (disable (:e feat->ilen))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32i-le ()
  :returns (feat featp)
  :short "Features for RV32I, with little endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32i-be ()
  :returns (feat featp)
  :short "Features for RV32I, with big endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64i-le ()
  :returns (feat featp)
  :short "Features for RV64I, with little endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64i-be ()
  :returns (feat featp)
  :short "Features for RV64I, with big endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32e-le ()
  :returns (feat featp)
  :short "Features for RV32E, with little endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32e-be ()
  :returns (feat featp)
  :short "Features for RV32E, with big endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64e-le ()
  :returns (feat featp)
  :short "Features for RV64E, with little endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-little)
             :m nil))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64e-be ()
  :returns (feat featp)
  :short "Features for RV64E, with big endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-big)
             :m nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32im-le ()
  :returns (feat featp)
  :short "Features for RV32IM, with little endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32im-be ()
  :returns (feat featp)
  :short "Features for RV32IM, with big endian memory."
  (make-feat :base (feat-base-rv32i)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64im-le ()
  :returns (feat featp)
  :short "Features for RV64IM, with little endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64im-be ()
  :returns (feat featp)
  :short "Features for RV64IM, with big endian memory."
  (make-feat :base (feat-base-rv64i)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv32em-le ()
  :returns (feat featp)
  :short "Features for RV32EM, with little endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv32em-be ()
  :returns (feat featp)
  :short "Features for RV32EM, with big endian memory."
  (make-feat :base (feat-base-rv32e)
             :endian (feat-endian-big)
             :m t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define feat-rv64em-le ()
  :returns (feat featp)
  :short "Features for RV64EM, with little endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-little)
             :m t))

;;;;;;;;;;;;;;;;;;;;

(define feat-rv64em-be ()
  :returns (feat featp)
  :short "Features for RV64EM, with big endian memory."
  (make-feat :base (feat-base-rv64e)
             :endian (feat-endian-big)
             :m t))
