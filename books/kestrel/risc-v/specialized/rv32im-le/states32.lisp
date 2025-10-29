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
  :short "Specialization of (@see states) to RV32IM little endian."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a recognizer for the valid states for the RV32I base;
     in our current model, the states do not depend
     on (the presence of absence of) the M extension
     or on the endianness.
     We introduce a fixtype that is isomorphic to that recognizer.
     We specialize the operations on states to operate on that fixtype.
     This is work in progress.")
   (xdoc::p
    "Along with the model of states, which we take from @(see states32i),
     we define some operations on the states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of states with base RV32I."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32im-le)))

  ///

  (defruled unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
    (implies (and (stat-validp stat (feat-rv32im-le))
                  (natp reg)
                  (< reg 32))
             (unsigned-byte-p 32 (nth (1- reg) (stat->xregs stat))))
    :enable (stat-validp nfix (:e feat-rv32im-le))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len xregs32i
  :short "Fixtype of the @('x') registers for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of 31 unsigned 32-bit integers,
     according to @(tsee stat) and @(tsee stat-validp).
     Recall that @('x0') is always 0 and thus not explicitly modeled."))
  :list-type ubyte32-list
  :length 31
  :pred xregs32ip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len memory32i
  :short "Fixtype of memories for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of @($2^{32}$) unsigned 8-bit integers,
     according to @(tsee stat) and @(tsee stat-validp).
     Recall that we do not model restrictions on the address space yet."))
  :list-type ubyte8-list
  :length 4294967296 ; (expt 2 32)
  :pred memory32ip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stat32i
  :short "Fixtype of states for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee stat)
     according to @(tsee stat-validp)."))
  ((xregs xregs32i)
   (pc ubyte32)
   (memory memory32i)
   (error bool))
  :pred stat32ip

  :prepwork ((local (in-theory (enable (:e tau-system)))))

  ///

  (defrule len-of-stat32i->xregs
    (equal (len (stat32i->xregs stat))
           31))

  (defrule len-of-stat32i->memory
    (equal (len (stat32i->memory stat))
           4294967296)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat32i-from-stat ((stat stat-rv32i-p))
  :returns (stat32i stat32ip)
  :short "Convert from @(tsee stat-rv32i-p) to @(tsee stat32i)."
  (make-stat32i :xregs (stat->xregs stat)
                :pc (stat->pc stat)
                :memory (stat->memory stat)
                :error (stat->error stat))
  :guard-hints
  (("Goal"
    :in-theory (enable stat-rv32i-p
                       stat-validp
                       xregs32ip
                       acl2::ubyte32-listp-rewrite-unsigned-byte-listp
                       memory32ip
                       ubyte32p
                       (:e feat-rv32im-le)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-from-stat32i ((stat32i stat32ip))
  :returns (stat stat-rv32i-p
                 :hints
                 (("Goal"
                   :in-theory
                   (enable stat-rv32i-p
                           stat-validp
                           acl2::unsigned-byte-listp-rewrite-ubyte32-listp
                           acl2::unsigned-byte-p-rewrite-ubyte32p
                           (:e feat-rv32im-le)))))
  :short "Convert from @(tsee stat32i) to @(tsee stat-rv32i-p)."
  (make-stat :xregs (stat32i->xregs stat32i)
             :pc (stat32i->pc stat32i)
             :memory (stat32i->memory stat32i)
             :error (stat32i->error stat32i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stat32i-iso
  :short "Isomorphism between @(tsee stat-rv32i-p) and @(tsee stat32i)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee stat32i-from-stat) and @(tsee stat-from-stat32i) functions
     are the isomorphic conversions."))

  (acl2::defiso stat32i-iso
    stat-rv32i-p
    stat32ip
    stat32i-from-stat
    stat-from-stat32i
    :thm-names (:beta-of-alpha stat-from-stat32i-of-stat32i-from-stat
                :alpha-of-beta stat32i-from-stat-of-stat-from-stat32i
                :alpha-injective stat32i-from-stat-injective
                :beta-injective stat-from-stat32i-injective)
    :hints (:beta-of-alpha (("Goal" :in-theory (enable stat-from-stat32i
                                                       stat32i-from-stat
                                                       stat-rv32i-p
                                                       xregs32ip
                                                       memory32ip
                                                       (:e feat-rv32im-le))))
            :alpha-of-beta (("Goal" :in-theory (enable stat-from-stat32i
                                                       stat32i-from-stat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{0}
  :short "Partially evaluate @(tsee read-xreg-unsigned)
          for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick @(tsee feat-rv32im-le),
     but we could have picked any of the variants for RV32I."))

  (apt::parteval read-xreg-unsigned
                 ((feat (feat-rv32im-le)))
                 :new-name read32i-xreg-unsigned{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{1}
  :short "Simplify @(tsee read32i-xreg-unsigned{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can eliminate the fixers."))

  (apt::simplify read32i-xreg-unsigned{0}
    :new-name read32i-xreg-unsigned{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable (unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
             (:e feat-rv32im-le))
    :disable (lnfix
              unsigned-byte-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned{2}
  :short "Refine @(tsee read32i-xreg-unsigned{1})
          to use the isomorphic states @(tsee stat32i)."

  (apt::isodata read32i-xreg-unsigned{1}
                ((stat stat32i-iso))
                :undefined 0
                :new-name read32i-xreg-unsigned{2}
                :hints (("Goal" :in-theory (enable stat-rv32i-p
                                                   (:e feat-rv32im-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-unsigned
  :short "Simplify @(tsee read32i-xreg-unsigned{2})
          after the isomorphic state transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we eliminate
     the outer @(tsee if) with @(tsee mbt) added by @(tsee apt::isodata).")
   (xdoc::p
    "We simplify the guard to eliminate @(tsee stat-validp) from it,
     which is implied by @(tsee stat32ip).")
   (xdoc::p
    "This is the final refinement for this function,
     so we use the name @('read32i-xreg-unsigned') without numeric index."))

  (apt::simplify read32i-xreg-unsigned{2}
    :new-name read32i-xreg-unsigned
    :assumptions :guard
    :simplify-guard t
    :thm-enable nil
    :enable (stat-from-stat32i
             stat-validp
             unsigned-byte-p-32-of-nth-of-stat-rv32i->xregs
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p))

  (defrule ubyte32p-of-read32i-xreg-unsigned
    (implies (and (natp reg)
                  (< reg 32))
             (ubyte32p (read32i-xreg-unsigned reg stat)))
    :enable (read32i-xreg-unsigned nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled read-xreg-unsigned-to-read32i-xreg-unsigned
  :short "Rewriting of @(tsee read-xreg-unsigned)
          to @(tsee read32i-xreg-unsigned)."
  (implies (and (statp stat)
                (equal feat (feat-rv32im-le))
                (stat-validp stat feat)
                (natp reg)
                (< reg 32))
           (equal (read-xreg-unsigned reg stat feat)
                  (read32i-xreg-unsigned reg (stat32i-from-stat stat))))
  :enable (read-xreg-unsigned-becomes-read32i-xreg-unsigned{0}
           read32i-xreg-unsigned{0}-becomes-read32i-xreg-unsigned{1}
           read32i-xreg-unsigned{1}-to-read32i-xreg-unsigned{2}
           read32i-xreg-unsigned{2}-becomes-read32i-xreg-unsigned
           (:e feat-rv32im-le)
           stat-rv32i-p
           stat-from-stat32i-of-stat32i-from-stat
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{0}
  :short "Partially evaluate @(tsee read-xreg-unsigned)
          for the RV32I base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick @(tsee feat-rv32im-le),
     but we could have picked any of the variants for RV32I."))

  (apt::parteval read-xreg-signed
                 ((feat (feat-rv32im-le)))
                 :new-name read32i-xreg-signed{0}
                 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{1}
  :short "Simplify @(tsee read32i-xreg-signed{0}) after partial evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assume the guard so that we can replace @('XLEN') with 32."))

  (apt::simplify read32i-xreg-signed{0}
    :new-name read32i-xreg-signed{1}
    :simplify-guard t
    :assumptions :guard
    :thm-enable nil
    :enable ((:e feat-rv32im-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{2}
  :short "Refine @(tsee read32i-xreg-signed{1})
          to use the isomorphic states @(tsee stat32i)."

  (apt::isodata read32i-xreg-signed{1}
                ((stat stat32i-iso))
                :undefined 0
                :new-name read32i-xreg-signed{2}
                :hints (("Goal" :in-theory (enable stat-rv32i-p
                                                   (:e feat-rv32im-le))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed{3}
  :short "Simplify the body of @(tsee read32i-xreg-signed{2})
          to call @(tsee read32i-xreg-unsigned)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee read-xreg-unsigned-to-read32i-xreg-unsigned)
     to accomplish that rewriting.
     Note that this eliminates the isomorphic conversion."))

  (apt::simplify read32i-xreg-signed{2}
    :new-name read32i-xreg-signed{3}
    :assumptions :guard
    :thm-enable nil
    :enable (read-xreg-unsigned-to-read32i-xreg-unsigned
             stat32i-from-stat-of-stat-from-stat32i
             (:e feat-rv32im-le))
    :disable (logext)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read32i-xreg-signed
  :short "Simplify the guard of @(tsee read32i-xreg-signed{3})
          to eliminate the isomorphic conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "We had to do this simplication separately from the previous one
     because the rules needed to do the rewritings interfere."))

  (apt::simplify read32i-xreg-signed{3}
    :new-name read32i-xreg-signed
    :assumptions :guard
    :simplify-guard t
    :simplify-body nil
    :thm-enable nil
    :enable (stat-from-stat32i
             stat-validp
             acl2::unsigned-byte-listp-rewrite-ubyte32-listp
             acl2::unsigned-byte-p-rewrite-ubyte32p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-xreg-unsigned ((reg ubyte5p) (stat stat32ip))
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
      (nth (1- reg) (stat32i->xregs stat))))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system))))

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (e/d ((:e tau-system))
                                        (read32-xreg-unsigned)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-xreg-signed ((reg ubyte5p) (stat stat32ip))
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

(define write32-xreg ((reg ubyte5p) (val integerp) (stat stat32ip))
  :returns (new-stat stat32ip)
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
        (stat32i-fix stat)
      (change-stat32i stat :xregs (update-nth (1-  reg)
                                              (loghead 32 val)
                                              (stat32i->xregs stat)))))
  :guard-hints (("Goal" :in-theory (enable xregs32ip
                                           stat32ip
                                           stat32i->xregs
                                           ubyte5p
                                           nfix
                                           max)))
  ///
  (fty::deffixequiv write32-xreg
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-pc ((stat stat32ip))
  :returns (pc ubyte32p)
  :short "Read the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an unsigned 32-bit integer,
     read directly from the register."))
  (stat32i->pc stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-pc ((pc integerp) (stat stat32ip))
  :returns (new-stat stat32ip)
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
  (change-stat32i stat :pc (loghead 32 pc))
  ///
  (fty::deffixequiv write32-pc
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc32-pc ((stat stat32ip))
  :returns (new-stat stat32ip)
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

(define read32-mem-ubyte8 ((addr integerp) (stat stat32ip))
  :returns (val ubyte8p :hints (("Goal" :in-theory (enable nfix))))
  :short "Read an unsigned 8-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer, which we turn into a 32-bit unsigned address.
     We return the byte at that memory address, directly."))
  (b* ((addr (loghead 32 addr)))
    (nth addr (stat32i->memory stat)))
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

(define read32-mem-ubyte16-lendian ((addr integerp) (stat stat32ip))
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

(define read32-mem-ubyte32-lendian ((addr integerp) (stat stat32ip))
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

(define write32-mem-ubyte8 ((addr integerp) (val ubyte8p) (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Write an unsigned 8-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer,
     which we turn into a 32-bit unsigned address."))
  (change-stat32i stat :memory (update-nth (loghead 32 addr)
                                           (loghead 8 val)
                                           (stat32i->memory stat)))
  :guard-hints (("Goal" :in-theory (enable memory32ip nfix max (:e tau-system))))
  :hooks nil ; does not fix val

  ///

  (fty::deffixequiv write32-mem-ubyte8
    :args ((addr integerp) (stat stat32ip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte16-lendian ((addr integerp)
                                     (val ubyte16p)
                                     (stat stat32ip))
  :returns (new-stat stat32ip
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
    :args ((addr integerp) (stat stat32ip))
    :hints (("Goal" :in-theory (disable acl2::loghead-loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte32-lendian ((addr integerp)
                                     (val ubyte32p)
                                     (stat stat32ip))
  :returns (new-stat stat32ip
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
    :args ((addr integerp) (stat stat32ip))
    :hints (("Goal" :in-theory (disable acl2::loghead-loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32p ((stat stat32ip))
  :returns (yes/no booleanp)
  :short "Check if the error flag in the state is set."
  (stat32i->error stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32 ((stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Set the error flag in the state."
  (change-stat32i stat :error t))
