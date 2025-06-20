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

(include-book "../library-extensions/logappn")

(include-book "centaur/bitops/part-select" :dir :system)
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte32-list" :dir :system)
(include-book "kestrel/fty/ubyte32-option" :dir :system)
(include-book "kestrel/fty/ubyte64-list" :dir :system)
(include-book "kestrel/utilities/unsigned-byte-fixing" :dir :system)

(local (include-book "../library-extensions/theorems"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/sbyte32-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte32-ihs-theorems" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states
  :parents (specification)
  :short "Model of states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a model of states,
     along with operations on those states.
     We capture all possible states for all possible RISC-V features,
     but we also introduce a predicate saying when a state
     is valid with respect to given features."))
  :default-parent t
  :order-subtopics t)

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
     which is 32 in RV32I/RV32E, or 64 in RV64I/RV64E.
     The number of registers is 32 or 16,
     based on whether the base is RV32I/RV64I or RV32R/RV64E.
     In @(tsee stat-validp),
     we constrain this state component to be
     a list of appropriate type and appropriate length;
     thus, we do not need to constrain it at all here.")
   (xdoc::p
    "The program counter @('pc') has the same size @('XLEN')
     as the @('x') registers.
     In @(tsee stat-validp),
     we constrain this state component to be
     an integer in the appropriate range;
     thus, we do not need to constrain it at all here.")
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
    "The features dictate
     the size @('XLEN') of the registers, either 32 or 64 bits,
     so we constrain them to form a list of 32-bit or 64-bit unsigned values.
     The number of registers is @(tsee feat->xnum), either 32 or 16,
     also based on the features.
     However, since @('x0') is hardwired to 0 [ISA:2.1],
     we do not model that register explicitly:
     we only model @('x1'), @('x2'), etc.;
     so we constrain the length of the list to be
     one less than the actual number of registers.")
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
         (equal (len stat.xregs) (1- xnum))
         (unsigned-byte-p xlen stat.pc)
         (equal (len stat.memory) (expt 2 xlen))))
  :hooks (:fix)

  ///

  (defrule true-listp-of-stat->xregs
    (implies (stat-validp stat feat)
             (true-listp (stat->xregs stat)))
    :rule-classes :type-prescription)

  (defrule unsigned-byte-listp-of-stat->xregs
    (implies (stat-validp stat feat)
             (unsigned-byte-listp (feat->xlen feat)
                                  (stat->xregs stat))))

  (defrule ubyte32-listp-of-stat->xregs-when-32p
    (implies (and (stat-validp stat feat)
                  (feat-32p feat))
             (ubyte32-listp (stat->xregs stat)))
    :hints
    (("Goal"
      :in-theory (enable acl2::ubyte32-listp-rewrite-unsigned-byte-listp))))

  (defrule ubyte64-listp-of-stat->xregs-when-64p
    (implies (and (stat-validp stat feat)
                  (feat-64p feat))
             (ubyte64-listp (stat->xregs stat)))
    :hints
    (("Goal"
      :in-theory (enable acl2::ubyte64-listp-rewrite-unsigned-byte-listp))))

  (defrule len-of-stat->xregs
    (implies (stat-validp stat feat)
             (equal (len (stat->xregs stat))
                    (1- (feat->xnum feat))))
    :hints (("Goal" :in-theory (enable feat->xnum))))

  (defrule unsigned-byte-p-of-stat->pc
    (implies (stat-validp stat feat)
             (unsigned-byte-p (feat->xlen feat)
                              (stat->pc stat))))

  (defrule ubyte32p-of-stat->pc-when-32p
    (implies (and (stat-validp stat feat)
                  (feat-32p feat))
             (ubyte32p (stat->pc stat)))
    :hints (("Goal" :in-theory (enable ubyte32p))))

  (defrule ubyte64p-of-stat->pc-when-64p
    (implies (and (stat-validp stat feat)
                  (feat-64p feat))
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
  :returns (val (unsigned-byte-p (feat->xlen feat) val))
  :short "Read an unsigned integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The index must be less than the number @('n') of registers,
     so that the registers @('x0') to @('x<n-1>') can be indexed.
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
      (unsigned-byte-fix (feat->xlen feat)
                         (nth (1- reg) (stat->xregs stat)))))
  :hooks (:fix)
  :type-prescription (natp (read-xreg-unsigned reg stat feat))

  ///

  (defret ubyte32p-of-read-xreg-unsigned-when-32p
    (ubyte32p val)
    :hyp (feat-32p feat)
    :hints (("Goal"
             :use return-type-of-read-xreg-unsigned
             :in-theory (e/d (ubyte32p)
                             (read-xreg-unsigned
                              return-type-of-read-xreg-unsigned)))))

  (defret ubyte64p-of-read-xreg-unsigned-when-64p
    (ubyte64p val)
    :hyp (feat-64p feat)
    :hints (("Goal"
             :use return-type-of-read-xreg-unsigned
             :in-theory (e/d (ubyte64p)
                             (read-xreg-unsigned
                              return-type-of-read-xreg-unsigned)))))

  (defrule read-xreg-unsigned-of-x0
    (equal (read-xreg-unsigned 0 stat feat)
           0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-signed ((reg natp) (stat statp) (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (val (signed-byte-p (feat->xlen feat) val))
  :short "Read a signed integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read an unsigned integer,
     and we convert it to signed according to @('XLEN').")
   (xdoc::p
    "This is a convenience operation, to interpret registers as signed,
     even though their representation in the state is always unsigned.
     Several instructions interpret registers as signed."))
  (logext (feat->xlen feat)
          (read-xreg-unsigned reg stat feat))
  :hooks (:fix)
  :type-prescription (integerp (read-xreg-signed reg stat feat))

  ///

  (defret sbyte32p-of-read-xreg-signed-when-32p
    (sbyte32p val)
    :hyp (feat-32p feat)
    :hints (("Goal"
             :use return-type-of-read-xreg-signed
             :in-theory (e/d (sbyte32p)
                             (read-xreg-signed
                              return-type-of-read-xreg-signed)))))

  (defret sbyte64p-of-read-xreg-signed-when-64p
    (sbyte64p val)
    :hyp (feat-64p feat)
    :hints (("Goal"
             :use return-type-of-read-xreg-signed
             :in-theory (e/d (sbyte64p)
                             (read-xreg-signed
                              return-type-of-read-xreg-signed)))))

  (defrule read-xreg-signed-of-x0
    (equal (read-xreg-signed 0 stat feat)
           0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-unsigned32 ((reg natp) (stat statp) (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (val ubyte32p)
  :short "Read an unsigned 32-bit integer from a 64-bit @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only defined when @('XLEN') is 64;
     when it is 32, @(tsee read-xreg-unsigned) already returns a 32-bit integer.
     When @('XLEN') is 64,
     several instructions read the low 32 bits of a register;
     so it is useful to introduce this abbreviation,
     which reads the whole integer and keeps the low 32 bits."))
  (loghead 32 (read-xreg-unsigned reg stat feat))
  :hooks (:fix)
  :type-prescription (natp (read-xreg-unsigned32 reg stat feat))

  ///

  (defrule read-xreg-unsigned32-of-x0
    (equal (read-xreg-unsigned32 0 stat feat)
           0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-signed32 ((reg natp) (stat statp) (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (val sbyte32p)
  :short "Read a signed 32-bit integer from a 64-bit @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee read-xreg-unsigned32) in purpose,
     but it is useful when the 32 bits of the register
     are treated as a signed integer instead of unsigned."))
  (logext 32 (read-xreg-unsigned reg stat feat))
  :hooks (:fix)
  :type-prescription (integerp (read-xreg-signed32 reg stat feat))

  ///

  (defrule read-xreg-signed32-of-x0
    (equal (read-xreg-signed32 0 stat feat)
           0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-xreg ((reg natp) (val integerp) (stat statp) (feat featp))
  :guard (and (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Write an integer to an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The integer may have any size:
     we only keep its low @('XLEN') bits,
     and write those to the register.")
   (xdoc::p
    "The index must be less than the number @('n') of registers,
     so that the registers @('x0') to @('x<n-1>') can be indexed.")
   (xdoc::p
    "As explained in @(tsee stat),
     @('x0') is not modeled explicitly, since it is hardwired to 0.
     Thus, the 0 index is treated separately;
     the other cases are handled by decrementing the index by 1."))
  (b* ((reg (lnfix reg)))
    (if (= reg 0)
        (stat-fix stat)
      (change-stat stat :xregs (update-nth (1- reg)
                                           (loghead (feat->xlen feat) val)
                                           (stat->xregs stat)))))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-xreg
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
    :hints (("Goal" :in-theory (enable stat-validp fix max))))

  (defrule write-xreg-of-x0
    (equal (write-xreg 0 val stat feat)
           (stat-fix stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-xreg-32 ((reg natp) (val integerp) (stat statp) (feat featp))
  :guard (and (feat-64p feat)
              (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat)))
  :returns (new-stat statp)
  :short "Write an integer to the low 32 bit of a 64-bit @('x') register,
          sign-extending to the high 32 bits of the register."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is is only defined when @('XLEN') is 64;
     when it is 32, @(tsee write-xreg) already writes all 32 bits.
     When @('XLEN') is 64,
     several instructions write to the low 32 bits of a register,
     sign-extending to the high 32 bits;
     so it is useful to introduce this abbreviation,
     which takes an integer of any size,
     keeps the low 32 bits,
     and writes their sign extension to the register."))
  (write-xreg reg (logext 32 val) stat feat)
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-xreg-32
    (stat-validp new-stat feat)
    :hyp (and (stat-validp stat feat)
              (< (lnfix reg) (feat->xnum feat))))

  (defrule write-xreg-32-of-x0
    (equal (write-xreg-32 0 val stat feat)
           (stat-fix stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-pc ((stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (pc (unsigned-byte-p (feat->xlen feat) pc))
  :short "Read the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is always an unsigned @('XLEN')-bit integer,
     which is an address in memory;
     recall that the memory address space goes from 0 to @('2^XLEN - 1'),
     as explained in @(tsee stat)."))
  (unsigned-byte-fix (feat->xlen feat)
                     (stat->pc stat))
  :hooks (:fix)
  :type-prescription (natp (read-pc stat feat))

  ///

  (defret ubyte32p-of-read-pc-when-32p
    (ubyte32p pc)
    :hyp (and (stat-validp stat feat)
              (feat-32p feat)))

  (defret ubyte64p-of-read-pc-when-64p
    (ubyte64p pc)
    :hyp (and (stat-validp stat feat)
              (feat-64p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-pc ((pc natp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Write the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass an unsigned integer of arbitrary size,
     of which only the low @('XLEN') bits are kept,
     and written to the program counter register.")
   (xdoc::p
    "[ISA:1.4] says that address computations wrap around ignoring overflow,
     i.e. the last address in the address space is adjacent to address 0.
     This function handles the wrapping around,
     see e.g. @(tsee inc4-pc)."))
  (change-stat stat :pc (loghead (feat->xlen feat) (lnfix pc)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-pc
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)
    :hints (("Goal" :in-theory (enable stat-validp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc4-pc ((stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Increment the program counter by 4."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the normal instruction encodings, instructions take 32 bits each.
     Thus, it is common to increment the program counter by 4 (bytes),
     which this function provides a concise way to do.")
   (xdoc::p
    "We read the program counter, we add 4, and we write the result.
     Recall that @(tsee write-pc) wraps around if needed [ISA:1.4]."))
  (write-pc (+ (read-pc stat feat) 4) stat feat)
  :hooks (:fix)

  ///

  (defret stat-validp-of-inc4-pc
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-memory-unsigned8 ((addr integerp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (val ubyte8p)
  :short "Read an unsigned 8-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is an integer of arbitrary size,
     of which we consider only the low @('XLEN') bits,
     as an unsigned address.
     Allowing any integer is convenient for callers.
     We return the byte at that address.")
   (xdoc::p
    "Since we read a single byte,
     there is no difference between little and big endian."))
  (b* ((addr (loghead (feat->xlen feat) addr)))
    (ubyte8-fix (nth addr (stat->memory stat))))
  :prepwork ((local (in-theory (enable loghead))))
  :guard-hints (("Goal" :in-theory (enable ifix stat-validp)))
  :hooks (:fix)
  :type-prescription (natp (read-memory-unsigned8 addr stat feat))

  ///

  (defret read-memory-unsigned8-upper-bound
    (<= val 255)
    :rule-classes :linear
    :hints (("Goal"
             :use ubyte8p-of-read-memory-unsigned8
             :in-theory (disable read-memory-unsigned8
                                 ubyte8p-of-read-memory-unsigned8)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-memory-unsigned16 ((addr integerp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (val ubyte16p
                :hints (("Goal" :in-theory (enable ubyte16p
                                                   unsigned-byte-p
                                                   integer-range-p
                                                   ifix))))
  :short "Read an unsigned 16-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we read that, and the subsequent byte.
     We form the 16-bit halfword based on endianness.")
   (xdoc::p
    "As in @(tsee read-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee read-memory-unsigned8) twice.
     Note that if @('addr') is @('2^XLEN - 1'),
     then @('addr + 1') wraps around to address 0."))
  (b* ((b0 (read-memory-unsigned8 addr stat feat))
       (b1 (read-memory-unsigned8 (+ (lifix addr) 1) stat feat)))
    (cond ((feat-little-endianp feat) (logappn 8 b0
                                               8 b1))
          ((feat-big-endianp feat) (logappn 8 b1
                                            8 b0))
          (t (impossible))))
  :hooks (:fix)

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (enable ifix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-memory-unsigned32 ((addr integerp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (val ubyte32p
                :hints (("Goal" :in-theory (enable ubyte32p
                                                   unsigned-byte-p
                                                   integer-range-p
                                                   ifix))))
  :short "Read an unsigned 32-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we read that, and the subsequent bytes.
     We form the 32-bit word based on endianness.")
   (xdoc::p
    "As in @(tsee read-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee read-memory-unsigned8) four times.
     Note that if @('addr') is close to @('2^XLEN - 1'),
     then the subsequent addresses may wrap around to addres 0."))
  (b* ((b0 (read-memory-unsigned8 addr stat feat))
       (b1 (read-memory-unsigned8 (+ (lifix addr) 1) stat feat))
       (b2 (read-memory-unsigned8 (+ (lifix addr) 2) stat feat))
       (b3 (read-memory-unsigned8 (+ (lifix addr) 3) stat feat)))
    (cond ((feat-little-endianp feat) (logappn 8 b0
                                               8 b1
                                               8 b2
                                               8 b3))
          ((feat-big-endianp feat) (logappn 8 b3
                                            8 b2
                                            8 b1
                                            8 b0))
          (t (impossible))))
  :hooks (:fix)

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (enable ifix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-memory-unsigned64 ((addr integerp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (val ubyte64p
                :hints (("Goal" :in-theory (enable ubyte64p
                                                   unsigned-byte-p
                                                   integer-range-p
                                                   ifix))))
  :short "Read an unsigned 64-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we read that, and the subsequent bytes.
     We form the 64-bit doubleword based on endianness.")
   (xdoc::p
    "As in @(tsee read-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee read-memory-unsigned8) four times.
     Note that if @('addr') is close to @('2^XLEN - 1'),
     then the subsequent addresses may wrap around to address 0."))
  (b* ((b0 (read-memory-unsigned8 addr stat feat))
       (b1 (read-memory-unsigned8 (+ (lifix addr) 1) stat feat))
       (b2 (read-memory-unsigned8 (+ (lifix addr) 2) stat feat))
       (b3 (read-memory-unsigned8 (+ (lifix addr) 3) stat feat))
       (b4 (read-memory-unsigned8 (+ (lifix addr) 4) stat feat))
       (b5 (read-memory-unsigned8 (+ (lifix addr) 5) stat feat))
       (b6 (read-memory-unsigned8 (+ (lifix addr) 6) stat feat))
       (b7 (read-memory-unsigned8 (+ (lifix addr) 7) stat feat)))
    (cond ((feat-little-endianp feat) (logappn 8 b0
                                               8 b1
                                               8 b2
                                               8 b3
                                               8 b4
                                               8 b5
                                               8 b6
                                               8 b7))
          ((feat-big-endianp feat) (logappn 8 b7
                                            8 b6
                                            8 b5
                                            8 b4
                                            8 b3
                                            8 b2
                                            8 b1
                                            8 b0))
          (t (impossible))))
  :hooks (:fix)

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (enable ifix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-memory-unsigned8 ((addr integerp)
                                (val ubyte8p)
                                (stat statp)
                                (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Write an unsigned 8-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is an integer of arbitrary size,
     of which we consider only the low @('XLEN') bits,
     as an unsigned address.
     Allowing any integer is convenient for callers.
     We write the byte at that address.")
   (xdoc::p
    "Since we write a single byte,
     there is no difference between little and big endian."))
  (b* ((addr (loghead (feat->xlen feat) addr)))
    (change-stat stat :memory (update-nth addr
                                          (ubyte8-fix val)
                                          (stat->memory stat))))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-memory-unsigned8
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)
    :hints (("Goal" :in-theory (enable stat-validp max)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-memory-unsigned16 ((addr integerp)
                                 (val ubyte16p)
                                 (stat statp)
                                 (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Write an unsigned 16-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we write that, and the subsequent byte.
     We write the bytes according to endianness.")
   (xdoc::p
    "As in @(tsee write-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee write-memory-unsigned8) twice.
     Note that if @('addr') is @('2^XLEN - 1'),
     then @('addr + 1') wraps around to address 0."))
  (b* ((val (ubyte16-fix val))
       (b0 (part-select val :low 0 :width 8))
       (b1 (part-select val :low 8 :width 8))
       ((mv 1st-byte 2nd-byte)
        (if (feat-little-endianp feat)
            (mv b0 b1)
          (mv b1 b0)))
       (stat (write-memory-unsigned8 addr 1st-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 1) 2nd-byte stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p
                                           unsigned-byte-p
                                           integer-range-p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-memory-unsigned16
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-memory-unsigned32 ((addr integerp)
                                 (val ubyte32p)
                                 (stat statp)
                                 (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Write an unsigned 32-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we write that, and the subsequent bytes.
     We write the bytes according to endianness.")
   (xdoc::p
    "As in @(tsee write-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee write-memory-unsigned8) twice.
     Note that if @('addr') is close to @('2^XLEN - 1'),
     then the subsequent addresses may wrap around to address 0."))
  (b* ((val (ubyte32-fix val))
       (b0 (part-select val :low 0 :width 8))
       (b1 (part-select val :low 8 :width 8))
       (b2 (part-select val :low 16 :width 8))
       (b3 (part-select val :low 24 :width 8))
       ((mv 1st-byte 2nd-byte 3rd-byte 4th-byte)
        (if (feat-little-endianp feat)
            (mv b0 b1 b2 b3)
          (mv b3 b2 b1 b0)))
       (stat (write-memory-unsigned8 addr 1st-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 1) 2nd-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 2) 3rd-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 3) 4th-byte stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p
                                           unsigned-byte-p
                                           integer-range-p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-memory-unsigned32
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-memory-unsigned64 ((addr integerp)
                                 (val ubyte64p)
                                 (stat statp)
                                 (feat featp))
  :guard (stat-validp stat feat)
  :returns (new-stat statp)
  :short "Write an unsigned 64-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The memory address is the one of the first byte;
     we write that, and the subsequent bytes.
     We write the bytes according to endianness.")
   (xdoc::p
    "As in @(tsee write-memory-unsigned8),
     we let the address be any integer.
     We use @(tsee write-memory-unsigned8) four times.
     Note that if @('addr') is close to @('2^XLEN - 1'),
     then the subsequent addresses may wrap around to address 0."))
  (b* ((val (ubyte64-fix val))
       (b0 (part-select val :low 0 :width 8))
       (b1 (part-select val :low 8 :width 8))
       (b2 (part-select val :low 16 :width 8))
       (b3 (part-select val :low 24 :width 8))
       (b4 (part-select val :low 32 :width 8))
       (b5 (part-select val :low 40 :width 8))
       (b6 (part-select val :low 48 :width 8))
       (b7 (part-select val :low 56 :width 8))
       ((mv 1st-byte 2nd-byte 3rd-byte 4th-byte
            5th-byte 6th-byte 7th-byte 8th-byte)
        (if (feat-little-endianp feat)
            (mv b0 b1 b2 b3 b4 b5 b6 b7)
          (mv b7 b6 b5 b4 b3 b2 b1 b0)))
       (stat (write-memory-unsigned8 addr 1st-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 1) 2nd-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 2) 3rd-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 3) 4th-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 4) 5th-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 5) 6th-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 6) 7th-byte stat feat))
       (stat (write-memory-unsigned8 (+ (lifix addr) 7) 8th-byte stat feat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p
                                           unsigned-byte-p
                                           integer-range-p)))
  :hooks (:fix)

  ///

  (defret stat-validp-of-write-memory-unsigned64
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-instruction ((addr integerp) (stat statp) (feat featp))
  :guard (stat-validp stat feat)
  :returns (val ubyte32-optionp
                :hints (("Goal" :in-theory (enable ubyte32p ifix))))
  :short "Read the 32-bit encoding of an instruction from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instructions are always stored in little endian [ISA:1.5],
     so the memory address is the one of the first byte;
     we read that, and the subsequent bytes.")
   (xdoc::p
    "As in @(tsee read-memory-unsigned8),
     we let the address be any integer,
     but we keep the low @('XLEN') bits,
     and we perform an alignment check [ISA:1.5];
     currently instructions must be always 4-byte-aligned,
     but see broader discussion in @(tsee feat->ialign).
     Note that @(tsee read-memory-unsigne8)
     already coerces the integer address to keep the low @('XLEN') bits,
     but we do that here too so we can do a clear alignment check;
     when we extend the model with
     the option to perform alignment checks on data read from memory [ISA:2.6],
     we may refactor the memory reading (and writing) functions,
     but for now what we have is fine for specification.")
   (xdoc::p
    "If the alignment check passes,
     we use @(tsee read-memory-unsigned8) four times.
     Note that if @('addr') is close to @('2^XLEN - 1'),
     then the subsequent addresses may wrap around to addres 0.")
   (xdoc::p
    "We return @('nil') if the first address is not 4-byte-aligned."))
  (b* ((addr (loghead (feat->xlen feat) addr))
       ((unless (= (mod addr 4) 0)) nil)
       (b0 (read-memory-unsigned8 addr stat feat))
       (b1 (read-memory-unsigned8 (+ addr 1) stat feat))
       (b2 (read-memory-unsigned8 (+ addr 2) stat feat))
       (b3 (read-memory-unsigned8 (+ addr 3) stat feat)))
    (logappn 8 b0
             8 b1
             8 b2
             8 b3))
  :hooks (:fix)

  ///

  (more-returns
   (val (or (natp val)
            (null val))
        :name natp-or-null-read-instruction
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (enable ifix)))))

  (more-returns
   (val ubyte32p
        :hyp (equal (mod (loghead (feat->xlen feat) addr) 4) 0)
        :hints (("Goal" :in-theory (enable ubyte32p ifix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define errorp ((stat statp) (feat featp))
  :guard (stat-validp stat feat)
  (declare (ignore feat))
  :returns (yes/no booleanp)
  :short "Check if the error flag in the state is set."
  (stat->error stat)
  :hooks (:fix)

  ///

  (defrule errorp-of-write-xreg
    (equal (errorp (write-xreg reg val stat feat) feat)
           (errorp stat feat))
    :enable write-xreg)

  (defrule errorp-of-write-xreg-32
    (equal (errorp (write-xreg-32 reg val stat feat) feat)
           (errorp stat feat))
    :disable errorp
    :enable write-xreg-32)

  (defrule errorp-of-write-pc
    (equal (errorp (write-pc pc stat feat) feat)
           (errorp stat feat))
    :enable write-pc)

  (defrule errorp-of-inc4-pc
    (equal (errorp (inc4-pc stat feat) feat)
           (errorp stat feat))
    :disable errorp
    :enable inc4-pc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error ((stat statp) (feat featp))
  :guard (stat-validp stat feat)
  (declare (ignore feat))
  :returns (new-stat statp)
  :short "Set the error flag in the state."
  (change-stat stat :error t)
  :hooks (:fix)

  ///

  (defret stat-validp-of-error
    (stat-validp new-stat feat)
    :hyp (stat-validp stat feat)
    :hints (("Goal" :in-theory (enable stat-validp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV32I(M) states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32i-le)))

  ///

  (defruled stat-rv32i-p-alt-def-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32i-be))))
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-le
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-le))))
    :enable stat-validp)

  (defruled stat-rv32i-p-alt-def-m-be
    (equal (stat-rv32i-p x)
           (and (statp x)
                (stat-validp x (feat-rv32im-be))))
    :enable stat-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64i-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV64I(M) states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv64i-le)))

  ///

  (defruled stat-rv64i-p-alt-def-be
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64i-be))))
    :enable stat-validp)

  (defruled stat-rv64i-p-alt-def-m-le
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64im-le))))
    :enable stat-validp)

  (defruled stat-rv64i-p-alt-def-m-be
    (equal (stat-rv64i-p x)
           (and (statp x)
                (stat-validp x (feat-rv64im-be))))
    :enable stat-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv32e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV32E states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv32e-le)))

  ///

  (defruled stat-rv32e-p-alt-def-be
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32e-be))))
    :enable stat-validp)

  (defruled stat-rv32e-p-alt-def-m-le
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-le))))
    :enable stat-validp)

  (defruled stat-rv32e-p-alt-def-m-be
    (equal (stat-rv32e-p x)
           (and (statp x)
                (stat-validp x (feat-rv32em-be))))
    :enable stat-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stat-rv64e-p (x)
  :returns (yes/no booleanp)
  :short "Recognizer of RV64E states."
  :long
  (xdoc::topstring
   (xdoc::p
    "These only depend on the base,
     not on the M extension or the endianness."))
  (and (statp x)
       (stat-validp x (feat-rv64e-be)))

  ///

  (defruled stat-rv64e-p-alt-def-be
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64e-be))))
    :enable stat-validp)

  (defruled stat-rv64e-p-alt-def-m-le
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64em-le))))
    :enable stat-validp)

  (defruled stat-rv64e-p-alt-def-m-be
    (equal (stat-rv64e-p x)
           (and (statp x)
                (stat-validp x (feat-rv64em-be))))
    :enable stat-validp))
