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

(include-book "states32i")

(include-book "../library-extensions/theorems")

(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte32-list" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/fty/sbyte32-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte16-ihs-theorems" :dir :system))
(local (include-book "kestrel/fty/ubyte32-ihs-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable ash ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states32
  :parents (rv32im)
  :short "Model of states for RV32IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "Along with the model of states, which we take from @(see states32i),
     we define some operations on the states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-xreg-unsigned ((reg ubyte5p) (stat stat32ip))
  :returns (val ubyte32p
                :hints (("Goal" :in-theory (enable ubyte5-fix ubyte5p))))
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
  :hooks (:fix)

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (disable read32-xreg-unsigned))))))

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
  (logext 32 (read32-xreg-unsigned reg stat))
  :hooks (:fix))

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
                                           ubyte5p)))
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
  (stat32i->pc stat)
  :hooks (:fix))

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
  (write32-pc (+ (read32-pc stat) 4) stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-mem-ubyte8 ((addr integerp) (stat stat32ip))
  :returns (val ubyte8p)
  :short "Read an unsigned 8-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer, which we turn into a 32-bit unsigned address.
     We return the byte at that memory address, directly."))
  (b* ((addr (loghead 32 addr)))
    (nth addr (stat32i->memory stat)))

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
  :returns (val ubyte16p :hints (("Goal" :in-theory (enable ubyte16p))))
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
       (ash b1 8)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read32-mem-ubyte32-lendian ((addr integerp) (stat stat32ip))
  :returns (val ubyte32p :hints (("Goal" :in-theory (enable ubyte32p))))
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
       (ash b3 24)))
  :hooks (:fix))

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
                                           (ubyte8-fix val)
                                           (stat32i->memory stat)))
  :guard-hints (("Goal" :in-theory (enable memory32ip)))

  ///

  (fty::deffixequiv write32-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte16-lendian ((addr integerp)
                                     (val ubyte16p)
                                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Write an unsigned 16-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the integer into bytes,
     and we write the low one at the given address,
     and the high one at the address just after that,
     which could be 0 if the given address is the last one in the space."))
  (b* ((val (ubyte16-fix val))
       (b0 (logand val #xff))
       (b1 (ash val -8))
       (stat (write32-mem-ubyte8 addr b0 stat))
       (stat (write32-mem-ubyte8 (1+ (ifix addr)) b1 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte16p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write32-mem-ubyte32-lendian ((addr integerp)
                                     (val ubyte32p)
                                     (stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Write an unsigned 32-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee write32-mem-ubyte16-lendian),
     but with 4 bytes instead of 2."))
  (b* ((val (ubyte32-fix val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (ash val -24))
       (stat (write32-mem-ubyte8 addr b0 stat))
       (stat (write32-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write32-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write32-mem-ubyte8 (+ 3 (ifix addr)) b3 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte32p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32p ((stat stat32ip))
  :returns (yes/no booleanp)
  :short "Check if the error flag in the state is set."
  (stat32i->error stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error32 ((stat stat32ip))
  :returns (new-stat stat32ip)
  :short "Set the error flag in the state."
  (change-stat32i stat :error t)
  :hooks (:fix))
