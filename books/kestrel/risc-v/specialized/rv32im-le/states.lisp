; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV32IM-LE")

(include-book "features")

(include-book "../../specification/states")

(include-book "kestrel/apt/isodata" :dir :system)
(include-book "kestrel/apt/parteval" :dir :system)
(include-book "kestrel/apt/simplify" :dir :system)
(include-book "kestrel/fty/deflist-of-len" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte32-list" :dir :system)
(include-book "std/util/defiso" :dir :system)

(local (include-book "../../library-extensions/logops-theorems"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/sbyte32-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte16-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte32-ihs-theorems" :dir :system))

(acl2::controlled-configuration)

(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rv32im-le-states
  :parents (specialized-rv32im-le)
  :short (xdoc::topstring
          "Specialization of "
          (xdoc::seetopic "riscv::states" "states")
          " to RV32IM little endian.")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for RV32IM little endian;
     in our current model, the states do not depend
     on (the presence of absence of) the M extension
     or on the endianness.
     We introduce a fixtype that is isomorphic to that recognizer.
     We specialize the operations on states to operate on that fixtype.
     This is work in progress.")
   (xdoc::p
    "Along with the model of states,
     we define some operations on the states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32im-le-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states for RV32IM little endian."
  (and (riscv::statp x)
       (riscv::stat-validp x (feat-rv32im-le)))

  ///

  (defruled unsigned-byte-p-32-of-nth-of-stat-rv32im-le->xregs
    (implies (and (riscv::stat-validp stat (feat-rv32im-le))
                  (natp reg)
                  (< reg 32))
             (unsigned-byte-p 32 (nth (1- reg) (riscv::stat->xregs stat))))
    :enable (riscv::stat-validp nfix (:e feat-rv32im-le))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len xregs
  :short "Fixtype of the @('x') registers for RV32IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of 31 unsigned 32-bit integers,
     according to @(tsee riscv::stat) and @(tsee riscv::stat-validp).
     Recall that @('x0') is always 0 and thus not explicitly modeled."))
  :list-type ubyte32-list
  :length 31
  :pred xregsp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len memory
  :short "Fixtype of memories fo RV32IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of @($2^{32}$) unsigned 8-bit integers,
     according to @(tsee riscv::stat) and @(tsee riscv::stat-validp).
     Recall that we do not model restrictions on the address space yet."))
  :list-type ubyte8-list
  :length 4294967296 ; (expt 2 32)
  :pred memoryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stat32
  :short "Fixtype of states for RV32IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee riscv::stat)
     according to @(tsee riscv::stat-validp)."))
  ((xregs xregs)
   (pc ubyte32)
   (memory memory)
   (error bool))
  :pred stat32p

  :prepwork ((local (in-theory (enable (:e tau-system)))))

  ///

  (defrule len-of-stat32->xregs
    (equal (len (stat32->xregs stat))
           31))

  (defrule len-of-stat32->memory
    (equal (len (stat32->memory stat))
           4294967296)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat32-from-stat ((stat stat-rv32im-le-p))
  :returns (stat32 stat32p)
  :short "Convert from @(tsee stat-rv32im-le-p) to @(tsee stat32)."
  (make-stat32 :xregs (riscv::stat->xregs stat)
                :pc (riscv::stat->pc stat)
                :memory (riscv::stat->memory stat)
                :error (riscv::stat->error stat))
  :guard-hints
  (("Goal"
    :in-theory (enable stat-rv32im-le-p
                       riscv::stat-validp
                       xregsp
                       acl2::ubyte32-listp-rewrite-unsigned-byte-listp
                       memoryp
                       ubyte32p
                       (:e feat-rv32im-le)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-from-stat32 ((stat32 stat32p))
  :returns (stat stat-rv32im-le-p
                 :hints
                 (("Goal"
                   :in-theory
                   (enable stat-rv32im-le-p
                           riscv::stat-validp
                           acl2::unsigned-byte-listp-rewrite-ubyte32-listp
                           acl2::unsigned-byte-p-rewrite-ubyte32p
                           (:e feat-rv32im-le)))))
  :short "Convert from @(tsee stat32) to @(tsee stat-rv32im-le-p)."
  (riscv::make-stat :xregs (stat32->xregs stat32)
                    :pc (stat32->pc stat32)
                    :memory (stat32->memory stat32)
                    :error (stat32->error stat32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stat32-iso
  :short "Isomorphism between @(tsee stat-rv32im-le-p) and @(tsee stat32)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee stat32-from-stat) and @(tsee stat-from-stat32) functions
     are the isomorphic conversions."))

  (acl2::defiso stat32-iso
    stat-rv32im-le-p
    stat32p
    stat32-from-stat
    stat-from-stat32
    :thm-names (:beta-of-alpha stat-from-stat32-of-stat32-from-stat
                :alpha-of-beta stat32-from-stat-of-stat-from-stat32
                :alpha-injective stat32-from-stat-injective
                :beta-injective stat-from-stat32-injective)
    :hints (:beta-of-alpha (("Goal" :in-theory (enable stat-from-stat32
                                                       stat32-from-stat
                                                       stat-rv32im-le-p
                                                       xregsp
                                                       memoryp
                                                       (:e feat-rv32im-le))))
            :alpha-of-beta (("Goal" :in-theory (enable stat-from-stat32
                                                       stat32-from-stat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-unsigned{0}
  :short "Partially evaluate @(tsee riscv::read-xreg-unsigned)
          for RV32IM little endian."

  (apt::parteval riscv::read-xreg-unsigned
                 ((riscv::feat (feat-rv32im-le)))
                 :new-name read32-xreg-unsigned{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-unsigned{1}
  :short "Simplify @(tsee read32-xreg-unsigned{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can eliminate the fixers."))

  (apt::simplify read32-xreg-unsigned{0}
    :new-name read32-xreg-unsigned{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable (unsigned-byte-p-32-of-nth-of-stat-rv32im-le->xregs
             (:e feat-rv32im-le))
    :disable (lnfix
              unsigned-byte-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-unsigned{2}
  :short "Refine @(tsee read32-xreg-unsigned{1})
          to use the isomorphic states @(tsee stat32)."

  (apt::isodata read32-xreg-unsigned{1}
                ((riscv::stat stat32-iso))
                :undefined 0
                :new-name read32-xreg-unsigned{2}
                :hints (("Goal" :in-theory (enable stat-rv32im-le-p
                                                   (:e feat-rv32im-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-unsigned{3}
  :short "Simplify @(tsee read32-xreg-unsigned{2})
          after the isomorphic state transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we eliminate
     the outer @(tsee if) with @(tsee mbt) added by @(tsee apt::isodata).")
   (xdoc::p
    "We simplify the guard to eliminate @(tsee riscv::stat-validp) from it,
     which is implied by @(tsee stat32p).")
   (xdoc::p
    "This is the final refinement for this function,
     so we use the name @('read32-xreg-unsigned') without numeric index."))

  (apt::simplify read32-xreg-unsigned{2}
    :new-name read32-xreg-unsigned{3}
    :assumptions :guard
    :simplify-guard t
    :thm-enable nil
    :enable (stat-from-stat32
             riscv::stat-validp
             unsigned-byte-p-32-of-nth-of-stat-rv32im-le->xregs
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p))

  (defrule ubyte32p-of-read32-xreg-unsigned{3}
    (implies (and (natp reg)
                  (< reg 32))
             (ubyte32p (read32-xreg-unsigned{3} reg stat)))
    :enable (read32-xreg-unsigned{3} nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled read-xreg-unsigned-to-read32-xreg-unsigned{3}
  :short "Rewriting of @(tsee riscv::read-xreg-unsigned)
          to @(tsee read32-xreg-unsigned{3})."
  (implies (and (riscv::statp stat)
                (equal feat (feat-rv32im-le))
                (riscv::stat-validp stat feat)
                (natp reg)
                (< reg 32))
           (equal (riscv::read-xreg-unsigned reg stat feat)
                  (read32-xreg-unsigned{3} reg (stat32-from-stat stat))))
  :enable (read-xreg-unsigned-becomes-read32-xreg-unsigned{0}
           read32-xreg-unsigned{0}-becomes-read32-xreg-unsigned{1}
           read32-xreg-unsigned{1}-to-read32-xreg-unsigned{2}
           read32-xreg-unsigned{2}-becomes-read32-xreg-unsigned{3}
           (:e feat-rv32im-le)
           stat-rv32im-le-p
           stat-from-stat32-of-stat32-from-stat
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-signed{0}
  :short "Partially evaluate @(tsee riscv::read-xreg-unsigned)
          for RV32IM little endian."

  (apt::parteval riscv::read-xreg-signed
                 ((riscv::feat (feat-rv32im-le)))
                 :new-name read32-xreg-signed{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-signed{1}
  :short "Simplify @(tsee read32-xreg-signed{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can replace @('XLEN') with 32."))

  (apt::simplify read32-xreg-signed{0}
    :new-name read32-xreg-signed{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable ((:e feat-rv32im-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-signed{2}
  :short "Refine @(tsee read32-xreg-signed{1})
          to use the isomorphic states @(tsee stat32)."

  (apt::isodata read32-xreg-signed{1}
                ((riscv::stat stat32-iso))
                :undefined 0
                :new-name read32-xreg-signed{2}
                :hints (("Goal" :in-theory (enable stat-rv32im-le-p
                                                   (:e feat-rv32im-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-signed{3}
  :short "Simplify the body of @(tsee read32-xreg-signed{2})
          to call @(tsee read32-xreg-unsigned{3})."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee read-xreg-unsigned-to-read32-xreg-unsigned{3})
     to accomplish that rewriting.
     Note that this eliminates the isomorphic conversion."))

  (apt::simplify read32-xreg-signed{2}
    :new-name read32-xreg-signed{3}
    :assumptions :guard
    :thm-enable nil
    :enable (read-xreg-unsigned-to-read32-xreg-unsigned{3}
             stat32-from-stat-of-stat-from-stat32
             (:e feat-rv32im-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32-xreg-signed{4}
  :short "Simplify the guard of @(tsee read32-xreg-signed{3})
          to eliminate the isomorphic conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "We had to do this simplication separately from the previous one
     because the rules needed to do the rewritings interfere."))

  (apt::simplify read32-xreg-signed{3}
    :new-name read32-xreg-signed{4}
    :assumptions :guard
    :simplify-guard t
    :simplify-body nil
    :thm-enable nil
    :enable (stat-from-stat32
             riscv::stat-validp
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-xreg-unsigned ((reg ubyte5p) (stat stat32p))
  :returns (val ubyte32p
                :hints (("Goal" :in-theory (enable ubyte5-fix ubyte5p nfix))))
  :short "Read an unsigned 32-bit integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     If the index is 0, we return 0,
     because @('x0') is always (implicitly) 0.
     Otherwise, we read the whole register (decreasing the index by 1),
     which is unsigned."))
  (b* ((reg (ubyte5-fix reg)))
    (if (= reg 0)
        0
      (nth (1- reg) (stat32->xregs stat))))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system))))

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (e/d ((:e tau-system))
                                        (read32-xreg-unsigned)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-xreg-signed ((reg ubyte5p) (stat stat32p))
  :returns (val sbyte32p)
  :short "Read a signed 32-bit integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     We read an unsigned 32-bit integer from the register,
     and convert it to signed."))
  (logext 32 (read32-xreg-unsigned reg stat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-xreg ((reg ubyte5p) (val integerp) (stat stat32p))
  :returns (new-stat stat32p)
  :short "Write a 32-bit integer to an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     If it is 0, there is no change, because @('x0') is always 0,
     and it is a no-op to write to it.
     If the index is not 0, we decrease it by 1,
     since the register file represents registers @('x1') to @('x31').")
   (xdoc::p
    "The value to write is actually any integer, signed or unsigned,
     of which we only write the low 32 bits into the register,
     as an unsigned 32-bit register.")
   (xdoc::p
    "The fact that the value to write is any integer is handy for callers,
     who can just pass the integer (e.g. the exact result of an operation)
     and let this writer function convert the integer for the register."))
  (b* ((reg (ubyte5-fix reg)))
    (if (= reg 0)
        (stat32-fix stat)
      (change-stat32 stat :xregs (update-nth (1-  reg)
                                              (loghead 32 val)
                                              (stat32->xregs stat)))))
  :guard-hints (("Goal" :in-theory (enable xregsp
                                           stat32p
                                           stat32->xregs
                                           ubyte5p
                                           nfix
                                           max)))
  ///
  (fty::deffixequiv write32-xreg
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-pc ((stat stat32p))
  :returns (pc ubyte32p)
  :short "Read the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an unsigned 32-bit integer,
     read directly from the register."))
  (stat32->pc stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-pc ((pc integerp) (stat stat32p))
  :returns (new-stat stat32p)
  :short "Write the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value is any integer, signed or unsigned,
     which is converted to an unsigned 32-bit integer
     by keeping its low 32 bits.")
   (xdoc::p
    "The fact that the value to write is any integer is handy for callers,
     who can just pass the integer (e.g. the exact result of an operation)
     and let this writer function convert the integer for the register.
     [ISA:1.4] says that address computations wrap round ignoring overflow,
     i.e. the last address in the address space is adjacent to address 0."))
  (change-stat32 stat :pc (loghead 32 pc))
  ///
  (fty::deffixequiv write32-pc
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc32-pc ((stat stat32p))
  :returns (new-stat stat32p)
  :short "Increment the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The increment is by 4, which is motivated by the fact that,
     at least in the normal encoding, instructions take 32 bits each.
     We may generalize this function, or add an alternative one,
     if and when we extend our model to support
     compressed encodings in the C extension [ISA:27].")
   (xdoc::p
    "We read the program counter, we add 4, and we write the result.
     Recall that @(tsee write32-pc) wraps around if needed [ISA:1.4]."))
  (write32-pc (+ (read32-pc stat) 4) stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-mem-ubyte8 ((addr integerp) (stat stat32p))
  :returns (val ubyte8p :hints (("Goal" :in-theory (enable nfix))))
  :short "Read an unsigned 8-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer, which we turn into a 32-bit unsigned address.
     We return the byte at that memory address, directly."))
  (b* ((addr (loghead 32 addr)))
    (nth addr (stat32->memory stat)))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system))))

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal"
                 :use ubyte8p-of-read32-mem-ubyte8
                 :in-theory (e/d (ubyte8p) (ubyte8p-of-read32-mem-ubyte8))))))

  (defret read32-mem-ubyte8-upper-bound
    (< val 256)
    :rule-classes :linear
    :hints (("Goal"
             :use ubyte8p-of-read32-mem-ubyte8
             :in-theory (e/d (ubyte8p) (ubyte8p-of-read32-mem-ubyte8)))))

  (fty::deffixequiv read32-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-mem-ubyte16-lendian ((addr integerp) (stat stat32p))
  :returns (val ubyte16p
                :hints (("Goal" :in-theory (enable ubyte16p
                                                   unsigned-byte-p
                                                   integer-range-p))))
  :short "Read an unsigned 16-bit little endian integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read the byte at the given address,
     and the byte at the address just after,
     which could be 0 if the given address is the last one in the space.
     We put the two bytes together in little endian order."))
  (b* ((b0 (read32-mem-ubyte8 addr stat))
       (b1 (read32-mem-ubyte8 (1+ (ifix addr)) stat)))
    (+ b0
       (ash b1 8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-mem-ubyte32-lendian ((addr integerp) (stat stat32p))
  :returns (val ubyte32p
                :hints (("Goal" :in-theory (enable ubyte32p
                                                   unsigned-byte-p
                                                   integer-range-p))))
  :short "Read an unsigned 32-bit little endian integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee read32-mem-ubyte16-lendian),
     but with 4 bytes instead of 2."))
  (b* ((b0 (read32-mem-ubyte8 addr stat))
       (b1 (read32-mem-ubyte8 (+ 1 (ifix addr)) stat))
       (b2 (read32-mem-ubyte8 (+ 2 (ifix addr)) stat))
       (b3 (read32-mem-ubyte8 (+ 3 (ifix addr)) stat)))
    (+ b0
       (ash b1 8)
       (ash b2 16)
       (ash b3 24))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte8 ((addr integerp) (val ubyte8p) (stat stat32p))
  :returns (new-stat stat32p)
  :short "Write an unsigned 8-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer,
     which we turn into a 32-bit unsigned address."))
  (change-stat32 stat :memory (update-nth (loghead 32 addr)
                                           (loghead 8 val)
                                           (stat32->memory stat)))
  :guard-hints (("Goal" :in-theory (enable memoryp nfix max (:e tau-system))))
  :hooks nil ; does not fix val

  ///

  (fty::deffixequiv write32-mem-ubyte8
    :args ((addr integerp) (stat stat32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte16-lendian ((addr integerp)
                                     (val ubyte16p)
                                     (stat stat32p))
  :returns (new-stat stat32p
                     :hints (("Goal" :in-theory (enable (:e tau-system)))))
  :short "Write an unsigned 16-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the integer into bytes,
     and we write the low one at the given address,
     and the high one at the address just after that,
     which could be 0 if the given address is the last one in the space."))
  (b* ((val (loghead 16 val))
       (b0 (logand val #xff))
       (b1 (ash val -8))
       (stat (write32-mem-ubyte8 addr b0 stat))
       (stat (write32-mem-ubyte8 (1+ (ifix addr)) b1 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p
                                           ubyte16p
                                           unsigned-byte-p
                                           integer-range-p)))
  :hooks nil ; does not fix val

  ///

  (fty::deffixequiv write32-mem-ubyte16-lendian
    :args ((addr integerp) (stat stat32p))
    :hints (("Goal" :in-theory (disable acl2::loghead-loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte32-lendian ((addr integerp)
                                     (val ubyte32p)
                                     (stat stat32p))
  :returns (new-stat stat32p
                     :hints (("Goal" :in-theory (enable (:e tau-system)))))
  :short "Write an unsigned 32-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee write32-mem-ubyte16-lendian),
     but with 4 bytes instead of 2."))
  (b* ((val (loghead 32 val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (ash val -24))
       (stat (write32-mem-ubyte8 addr b0 stat))
       (stat (write32-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write32-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write32-mem-ubyte8 (+ 3 (ifix addr)) b3 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p
                                           ubyte32p
                                           unsigned-byte-p
                                           integer-range-p)))
  :hooks nil ; does not fix val

  ///

  (fty::deffixequiv write32-mem-ubyte32-lendian
    :args ((addr integerp) (stat stat32p))
    :hints (("Goal" :in-theory (disable acl2::loghead-loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32p ((stat stat32p))
  :returns (yes/no booleanp)
  :short "Check if the error flag in the state is set."
  (stat32->error stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32 ((stat stat32p))
  :returns (new-stat stat32p)
  :short "Set the error flag in the state."
  (change-stat32 stat :error t))
