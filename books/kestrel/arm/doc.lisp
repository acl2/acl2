; A formal model of the ARM32 CPU
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "portcullis")
(include-book "step")
(include-book "xdoc/top" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(acl2::defxdoc arm32
  :short "A formal model of the ARM32 CPU."
  :parents (software-verification hardware-verification)
  :long
  (xdoc::topparas
    "The ARM32 model is an in-progress formal model of a 32-bit ARM CPU.  It
       attempts to formalize (some of) the <b>ARM Architecture Reference Manual,
       ARMv7-A and ARMv7-R edition</b>, which focuses on versions 4 through 7 of the
       ARM Architecture.

       The ARM32 model formalizes the state of the ARM32 CPU as well as the decoding and
       execution of instructions (how each instruction affects the CPU state).

       This model is intended for use with a forthcoming ARM32 variant of the
       @(see acl2::axe) toolkit."

    (xdoc::h3 "Modeling Approach")

    (xdoc::h4 "CPU State")

    "We model the state of the ARM CPU as an ACL2 single-threaded object (see
@(see acl2::stobj)).  The state has the following fields:"

    (xdoc::ul-from-string
      "The ARM core registers, an array of sixteen 32-bit unsigned values.

       The Application Program Status Register (APSR), a 32-bit unsigned value.

       The instruction set state register, a 2-bit unsigned value.  This
       selects between ARM, Thumb, Jazelle, and ThumbEE states.  Currently our
       model only defines the semantics of the ARM state.

       The IT block state register, an unsigned byte (not currently used as we
       do not yet model Thumb instructions).

       The endianness mapping register, a bit (currently our model only
       supports little-endian operation).

       The memory, an array of 2^32 8-bit bytes.

       An error flag, indicating whether an error has occurred.")

    (xdoc::h4 "Instruction Encodings")

    "Each instruction has one or more mnemonics, which are represented as keywords.
Different variants of an instruction have different mnemonics in our model.
For example, the EOR (exclusive or) instruction has 3 mnemonics:"

    (xdoc::ul-from-string
      ":eor-immediate

       :eor-register

       :eor-register-shifted-register")

    "Some instructions have multiple encodings.  For example, the @('ADR')
instruction has two encodings, A1 and A2.  We assign these separate mnemonics:"

    (xdoc::ul-from-string
      ":adr-encoding-a1

       :adr-encoding-a2")

    "(Currently our model includes only ARM encodings (A1, A2, etc.), not Thumb
     encodings (T1, T2, etc.).)

     We model the format of each instruction declaratively, by associating it
      with a formalized encoding diagram.  For example, our list of encodings
      contains the following entry:

       @({(:eor-immediate  (cond 4) 0 0 1 0 0 0 1 s (rn 4) (rd 4) (imm12 12))})

       which associates the @(':eor-immediate') instruction with the encoding diagram

       @({((cond 4) 0 0 1 0 0 0 1 s (rn 4) (rd 4) (imm12 12))})

       The formalized encoding diagram graphically depicts the layout of the 32
       bits in the instruction.

       A formalized encoding diagram can contain the following constructs:"

    (xdoc::ul-from-string
      "@('0') and @('1'), which represent themselves (bits in the encoding that must have those values).

         @('(0)') and @('(1)'), which represent values that \"should\" have those values.

         A list of the form @('(var n)'), which represents the variable @('var') in a
         field whose width is @('n') bits.  For example, @('(cond 4)')
         represents a 4-bit field whose name is @('cond').

         An underscore, @('_'), which is just a separator (essentially
         ignored).  We use it where two adjacent 0/1 values are in separate
         boxes in the informal diagram.

         A symbol other than @('_'), such as @('p'), which represents a 1-bit field of that name.")

    "Several checks are applied to the encoding diagrams, including:"

    (xdoc::ul-from-string
      "Each contains only supported elements (described above).

         Each represents exactly 32 bits.

         No instruction matches more than one encoding diagram, with some
         exceptions.  The exceptions represent cases where the same bit pattern
         can be interpreted as two different instructions.  Typically this
         corresponds to an instruction whose description in the ARM manual
         makes reference to another instruction.")

"The full list of encodings is:

@(def *patterns*)."

    (xdoc::h4 "Decoding Instructions")

    "Given formalized encoding diagrams for each instruction, our @('make-decoder')
      tool automatically generates a decoder.  The decoder takes a 4-byte value
      and determines which ARM instruction (if any) is represented. The
      function it generates is @('arm32-decode'):

@(def arm32-decode)

     "

    (xdoc::h4 "Instruction Semantic Functions")

    "The core of our ARM model is the collection of semantic functions, one per
mnemonic, that defines how executing each one affects the state of the ARM CPU.

     We created a tool, @('def-inst') to automate some of the boilerplate
     operations of each instruction.

For example, the following call to @('def-inst')

@({(def-inst :adc-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm))
             (arm (advance-pc arm)))
          arm))))})

causes this semantic function to be generated:

@(def execute-adc-immediate)

. The function generated by @('def-inst') combines the human-written model with the boilerplate code.  The
boilerplate code inserted by @('def-inst') does the following:"

    (xdoc::ul-from-string
      "Binds the values of various fields of the instruction (represented in the
       formalized encoding diagram) to their corresponding variables, which can
       then be mentioned in the human-written part of the semantic function.

       Optionally checks whether the @('cond') field of the instruction has the
       special value of @('#b1111'), which requires special handling for almost
       all instructions.

       Optionally handles the other possible values of the the @('cond') field,
       which determine whether the instruction should execute (for almost all
       instructions).

       Puts in the main body of the instruction (supplied by the human).

       Optionally, takes an equivalent definition of the instruction which may
       be more suitable for reasoning, proves it equivalent to the main body,
       and installs a rewrite rule to replace calls of the semantic function
       with the alternative body.")

    (xdoc::h4 "Step and Run Functions")

    "Our machinery automatically generates a dispatch function, @('execute-inst')
that, according to the instruction mnemonic, dispatches control to the
corresponding semantic function:

@(def execute-inst)

Our model includes a function, @('step') to fetch, decode, and execute a single instruction:

@(def step)

and a function, @('run') to run a given number of instructions:

@(def run)"

    (xdoc::h4 "More Information")

    "See the individual files in this directory for more documentation."
    ))

;; todo: link to axe/arm
