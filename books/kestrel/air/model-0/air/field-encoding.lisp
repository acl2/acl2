; AIR Library
; Model 0: PFCS Constraints
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "../language/abstract-syntax")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-encoding
  :parents (model-0)
  :short "Encoding of certain M0 language entities into the prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "The execution @(see traces) are encoded as constraints over the field,
     which means that the components of the traces
     are represented as field elements.")
   (xdoc::p
    "Program counters, which are natural numbers,
     are represented directly as field elements, which are also natural numbers.
     Assuming that the program is not unreasonably large,
     all its possible program counters fit into the field.")
   (xdoc::p
    "Accumulators, which are 8-bit natural numbers,
     are represented directly as field elements, which are also natural numbers.
     We just need to assume that the field prime is at least 255;
     in fact, it has to be larger than that for some constraints to work.")
   (xdoc::p
    "Halted flags, which are booleans,
     are readily represented as bits (0 or 1) as field elements.
     These are easy conversions.
     The library functions @(tsee bit->bool) and @(tsee bool->bit)
     can be used to convert between bits and booleans.")
   (xdoc::p
    "Opcodes are data structures,
     which we encode as natural numbers.
     Here we introduce functions to perform those conversions.")
   (xdoc::p
    "These encodings are independent from the specific field.
     They are more general than the "
    (xdoc::seetopic "field" "Koala Bear field")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define opcode-to-field ((opcode opcode-p))
  :returns (fe natp)
  :short "Encode an opcode into a field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fits into the field, so long as the prime is odd."))
  (opcode-case opcode
               :incr 0
               :decr 1
               :halt 2)

  ///

  (defret opcode-to-field-is-0/1/2
    (member-equal fe '(0 1 2)))

  (defret fep-of-opcode-to-field
    (pfield::fep fe prime)
    :hyp (and (dm::primep prime)
              (oddp prime))
    :hints (("Goal" :in-theory (enable pfield::fep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection opcode-list-to-field ((x program-p))
  :returns (fes nat-listp)
  :short "Lift @(tsee opcode-to-field) to programs,
          which are lists of opcodes."
  (opcode-to-field x)

  ///

  (defret fe-listp-of-opcode-list-to-field
    (pfield::fe-listp fes prime)
    :hyp (and (dm::primep prime)
              (oddp prime))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define opcode-from-field ((fe natp))
  :guard (member-equal fe '(0 1 2))
  :returns (opcode opcode-p)
  :short "Decode an opcode from a field element not exceeding 2."
  (case (nfix fe)
    (0 (opcode-incr))
    (1 (opcode-decr))
    (2 (opcode-halt))
    (t (prog2$ (acl2::impossible) (opcode-halt))))

  ///

  (defrule opcode-from-field-of-opcode-to-field
    (equal (opcode-from-field (opcode-to-field opcode))
           (opcode-fix opcode))
    :enable opcode-to-field)

  (defrule opcode-to-field-of-opcode-from-field
    (implies (member-equal fe '(0 1 2))
             (equal (opcode-to-field (opcode-from-field fe))
                    fe))
    :enable opcode-to-field))
