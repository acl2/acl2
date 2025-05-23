; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "library-extensions")

(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte64-list" :dir :system)
(include-book "kestrel/fty/deflist-of-len" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable ash ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states64
  :parents (rv64im)
  :short "Model of states for RV64IM."
  :long
  (xdoc::topstring
   (xdoc::p
    "Along with the model of states,
     we define some operations on the states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len xregfile64
  :short "Fixtype of the @('x') register file [ISA:2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are 32 registers, each of which consists of 64 bits.
     We model the content of each register as an unsigned 64-bit integer,
     which can be interpreted in different ways (see operations on states).")
   (xdoc::p
    "The @('x0') register is always 0; writing to it is a no-op.
     We build this invariant into this fixtype
     by only modeling 31 registers, namely @('x1') to @('x31'),
     and leaving @('x0') implicit."))
  :list-type ubyte64-list
  :length 31
  :pred xregfile64p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *mem64-size*
  :short "Size of (the address space of) the memory [ISA:1.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address space consists of 64 bits."))
  (expt 2 64))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(fty::deflist-of-len memory64
    :short "Fixtype of memories [ISA:1.4]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We model the memory as a list of @($2^{64}$) unsigned bytes,
       which can be interpreted in different ways (see operations on states).")
     (xdoc::p
      "This is the whole address space,
       although not all of it may be accessible,
       and parts of it may be dedicated to different purposes
       [ISA:1.4].
       Modeling these aspects
       (probably via some kind of parameterization of the model)
       is future work."))
    :list-type ubyte8-list
    :length ,*mem64-size*
    :pred memory64p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod state64
  :short "Fixtype of (unprivileged) processor states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the register file,
     the program counter
     (which is an unsigned 64-bit integer, addressing the memory space),
     and the memory.
     We also include a flag that is set when there is an error;
     this is an artifact of the model, not part of the RISC-V standard."))
  ((xregfile xregfile64)
   (pc ubyte64)
   (mem memory64)
   (error bool))
  :layout :list
  :tag :state64
  :pred state64p

  ///

  (defrule len-of-state64->xregfile
    (equal (len (state64->xregfile stat))
           31))

  (defrule len-of-state64->mem
    (equal (len (state64->mem stat))
           *mem64-size*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-xreg-unsigned ((reg ubyte5p) (stat state64p))
  :returns (val ubyte64p
                :hints (("Goal" :in-theory (enable ubyte5-fix ubyte5p))))
  :short "Read an unsigned 64-bit integer from an @('x') register."
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
      (nth (1- reg) (state64->xregfile stat))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-xreg-signed ((reg ubyte5p) (stat state64p))
  :returns (val sbyte64p)
  :short "Read a signed 64-bit integer from an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     We read an unsigned 64-bit integer from the register,
     and convert it to signed."))
  (logext 64 (read64-xreg-unsigned reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-xreg-unsigned32 ((reg ubyte5p) (stat state64p))
  :returns (val ubyte32p)
  :short "Read an unsigned 32-bit integer
          from the low bits of an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     We read an unsigned 64-bit integer from the register,
     and we keep the low 32 bits, stil unsigned."))
  (loghead 32 (read64-xreg-unsigned reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-xreg-signed32 ((reg ubyte5p) (stat state64p))
  :returns (val sbyte32p)
  :short "Read a signed 32-bit integer
          from the low bits of an @('x') register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.
     We read a signed 64-bit integer fromt he register,
     and we keep the low 32 bits, stil signed."))
  (logext 32 (read64-xreg-signed reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-xreg ((reg ubyte5p) (val integerp) (stat state64p))
  :returns (new-stat state64p)
  :short "Write a 64-bit integer to an @('x') register."
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
     of which we only write the low 64 bits into the register,
     as an unsigned 64-bit register.")
   (xdoc::p
    "The fact that the value to write is any integer is handy for callers,
     who can just pass the integer (e.g. the exact result of an operation)
     and let this writer function convert the integer for the register."))
  (b* ((reg (ubyte5-fix reg)))
    (if (= reg 0)
        (state64-fix stat)
      (change-state64 stat :xregfile (update-nth (1- reg)
                                                 (loghead 64 val)
                                                 (state64->xregfile stat)))))
  :guard-hints (("Goal" :in-theory (enable xregfile64p
                                           state64p
                                           state64->xregfile
                                           ubyte5p)))
  ///
  (fty::deffixequiv write64-xreg
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-xreg-32 ((reg ubyte5p) (val integerp) (stat state64p))
  :returns (new-stat state64p)
  :short "Write an integer to the low 32 bits of an @('x') register,
          sign-extending it to the high 32 bits of the register."
  :long
  (xdoc::topstring
   (xdoc::p
    "The register index consists of 5 bits.")
   (xdoc::p
    "The value to write is actually any integer, signed or unsigned,
     of which we only write the low 32 bits into the register,
     by converting it to a signed 32-bit integer,
     and then writing that to the register, which sign-extends it.")
   (xdoc::p
    "The fact that the value to write is any integer is handy for callers,
     who can just pass the integer (e.g. the exact result of an operation)
     and let this writer function convert the integer for the register."))
  (write64-xreg reg (logext 32 val) stat)
  ///
  (fty::deffixequiv write64-xreg-32
    :hints (("Goal" :in-theory (enable logext loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-pc ((stat state64p))
  :returns (pc ubyte64p)
  :short "Read the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is an unsigned 64-bit integer,
     read directly from the register."))
  (state64->pc stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-pc ((pc integerp) (stat state64p))
  :returns (new-stat state64p)
  :short "Write the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value is any integer, signed or unsigned,
     which is converted to an unsigned 64-bit integer
     by keeping its low 64 bits.")
   (xdoc::p
    "The fact that the value to write is any integer is handy for callers,
     who can just pass the integer (e.g. the exact result of an operation)
     and let this writer function convert the integer for the register.
     [ISA:1.4] says that address computations wrap round ignoring overflow,
     i.e. the last address in the address space is adjacent to address 0."))
  (change-state64 stat :pc (loghead 64 pc))
  ///
  (fty::deffixequiv write64-pc
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc64-pc ((stat state64p))
  :returns (new-stat state64p)
  :short "Increment the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The increment is by 4, which is motivated by the fact that,
     at least in the normal encoding, instructions take 32 bits each.
     We may generalize this function, or add an alternative one,
     if and when we extend our model to support
     compressed encodings in the C extension [ISA:26].")
   (xdoc::p
    "We read the program counter, we add 4, and we write the result.
     Recall that @(tsee write64-pc) wraps around if needed [ISA:1.4]."))
  (write64-pc (+ (read64-pc stat) 4) stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-mem-ubyte8 ((addr integerp) (stat state64p))
  :returns (val ubyte8p)
  :short "Read an unsigned 8-bit integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer, which we turn into a 64-bit unsigned address.
     We return the byte at that memory address, directly."))
  (b* ((addr (loghead 64 addr)))
    (nth addr (state64->mem stat)))

  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal"
                 :use ubyte8p-of-read64-mem-ubyte8
                 :in-theory (e/d (ubyte8p) (ubyte8p-of-read64-mem-ubyte8))))))

  (defret read64-mem-ubyte8-upper-bound
    (< val 256)
    :rule-classes :linear
    :hints (("Goal"
             :use ubyte8p-of-read64-mem-ubyte8
             :in-theory (e/d (ubyte8p) (ubyte8p-of-read64-mem-ubyte8)))))

  (fty::deffixequiv read64-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-mem-ubyte16-lendian ((addr integerp) (stat state64p))
  :returns (val ubyte16p :hints (("Goal" :in-theory (enable ubyte16p))))
  :short "Read an unsigned 16-bit little endian integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read the byte at the given address,
     and the byte at the address just after,
     which could be 0 if the given address is the last one in the space.
     We put the two bytes together in little endian order."))
  (b* ((b0 (read64-mem-ubyte8 addr stat))
       (b1 (read64-mem-ubyte8 (1+ (ifix addr)) stat)))
    (+ b0
       (ash b1 8)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-mem-ubyte32-lendian ((addr integerp) (stat state64p))
  :returns (val ubyte32p :hints (("Goal" :in-theory (enable ubyte32p))))
  :short "Read an unsigned 32-bit little endian integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee read64-mem-ubyte16-lendian),
     but with 4 bytes instead of 2."))
  (b* ((b0 (read64-mem-ubyte8 addr stat))
       (b1 (read64-mem-ubyte8 (+ 1 (ifix addr)) stat))
       (b2 (read64-mem-ubyte8 (+ 2 (ifix addr)) stat))
       (b3 (read64-mem-ubyte8 (+ 3 (ifix addr)) stat)))
    (+ b0
       (ash b1 8)
       (ash b2 16)
       (ash b3 24)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read64-mem-ubyte64-lendian ((addr integerp) (stat state64p))
  :returns (val ubyte64p :hints (("Goal" :in-theory (enable ubyte64p))))
  :short "Read an unsigned 64-bit little endian integer from memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee read64-mem-ubyte16-lendian)
     and @(tsee read64-mem-ubyte32-lendian),
     but with 8 bytes instead of 2 or 4."))
  (b* ((b0 (read64-mem-ubyte8 addr stat))
       (b1 (read64-mem-ubyte8 (+ 1 (ifix addr)) stat))
       (b2 (read64-mem-ubyte8 (+ 2 (ifix addr)) stat))
       (b3 (read64-mem-ubyte8 (+ 3 (ifix addr)) stat))
       (b4 (read64-mem-ubyte8 (+ 4 (ifix addr)) stat))
       (b5 (read64-mem-ubyte8 (+ 5 (ifix addr)) stat))
       (b6 (read64-mem-ubyte8 (+ 6 (ifix addr)) stat))
       (b7 (read64-mem-ubyte8 (+ 7 (ifix addr)) stat)))
    (+ b0
       (ash b1 8)
       (ash b2 16)
       (ash b3 24)
       (ash b4 32)
       (ash b5 40)
       (ash b6 48)
       (ash b7 56)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-mem-ubyte8 ((addr integerp) (val ubyte8p) (stat state64p))
  :returns (new-stat state64p)
  :short "Write an unsigned 8-bit integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "The address is any integer,
     which we turn into a 64-bit unsigned address."))
  (b* ((addr (loghead 64 addr)))
    (change-state64 stat :mem (update-nth (loghead 64 addr)
                                          (ubyte8-fix val)
                                          (state64->mem stat))))
  :guard-hints (("Goal" :in-theory (enable memory64p)))
  ///
  (fty::deffixequiv write64-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-mem-ubyte16-lendian ((addr integerp)
                                     (val ubyte16p)
                                     (stat state64p))
  :returns (new-stat state64p)
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
       (stat (write64-mem-ubyte8 addr b0 stat))
       (stat (write64-mem-ubyte8 (1+ (ifix addr)) b1 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte16p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-mem-ubyte32-lendian ((addr integerp)
                                     (val ubyte32p)
                                     (stat state64p))
  :returns (new-stat state64p)
  :short "Write an unsigned 32-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee write64-mem-ubyte16-lendian),
     but with 4 bytes instead of 2."))
  (b* ((val (ubyte32-fix val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (ash val -24))
       (stat (write64-mem-ubyte8 addr b0 stat))
       (stat (write64-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write64-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write64-mem-ubyte8 (+ 3 (ifix addr)) b3 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte32p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write64-mem-ubyte64-lendian ((addr integerp)
                                     (val ubyte64p)
                                     (stat state64p))
  :returns (new-stat state64p)
  :short "Write an unsigned 64-bit little endian integer to memory."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee write64-mem-ubyte16-lendian)
     and @(tsee write64-mem-ubyte32-lendian),
     but with 8 bytes instead of 2 or 4."))
  (b* ((val (ubyte64-fix val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (logand (ash val -24) #xff))
       (b4 (logand (ash val -32) #xff))
       (b5 (logand (ash val -40) #xff))
       (b6 (logand (ash val -48) #xff))
       (b7 (ash val -56))
       (stat (write64-mem-ubyte8 addr b0 stat))
       (stat (write64-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write64-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write64-mem-ubyte8 (+ 3 (ifix addr)) b3 stat))
       (stat (write64-mem-ubyte8 (+ 4 (ifix addr)) b4 stat))
       (stat (write64-mem-ubyte8 (+ 5 (ifix addr)) b5 stat))
       (stat (write64-mem-ubyte8 (+ 6 (ifix addr)) b6 stat))
       (stat (write64-mem-ubyte8 (+ 7 (ifix addr)) b7 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte64p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error64p ((stat state64p))
  :returns (yes/no booleanp)
  :short "Check if the error flag in the state is set."
  (state64->error stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error64 ((stat state64p))
  :returns (new-stat state64p)
  :short "Set the error flag in the state."
  (change-state64 stat :error t)
  :hooks (:fix))
