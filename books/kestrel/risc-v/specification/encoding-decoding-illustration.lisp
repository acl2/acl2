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

(include-book "xdoc/constructors" :dir :system)

(xdoc::add-resource-directory "kestrel-riscv-images" "../images")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc encoding-decoding-illustration
  :parents (encoding decoding)
  :short "Illustration of instruction encoding and decoding."
  :long
  (xdoc::topstring
   (xdoc::img :src "res/kestrel-riscv-images/encoding-decoding.png")
   (xdoc::p
    "The lighter blue oval consists of all instructions,
     i.e. all values of type @(tsee instr).")
   (xdoc::p
    "The lighter green oval consists of all 32-bit words,
     i.e. all values of type @(tsee ubyte32).")
   (xdoc::p
    "Given specific @(see features) @('feat'),
     the darker blue oval consists of all valid instructions,
     i.e. all values of type @(tsee instr)
     that additionally satisfy @(tsee instr-validp);
     this predicate depends on @('feat').")
   (xdoc::p
    "Given specific @(see features) @('feat'),
     the darker green oval consists of all valid instruction encodings,
     i.e. all values of type @(tsee ubyte32)
     that additionally satisfy @(tsee encoding-validp);
     this predicate depends on @('feat').")
   (xdoc::p
    "The `encode' arrow represents the function @(tsee encode),
     which maps each valid instruction to a valid encoding.
     The validity of the instruction is in the guard of @(tsee encode).
     The valid encodings are defined, via @(tsee encoding-validp),
     as the image of @(tsee encode) over the valid instructions:
     thus, the darker green oval is the image of
     the darker blue oval under @(tsee encode).")
   (xdoc::p
    "The upper `decode' arrow represents
     the witness function @('encoding-valid-witness')
     that accompanies @(tsee encoding-validp).
     Given a valid instruction encoding in the darker green oval,
     indicated by the dot in that oval,
     @('encoding-valid-witness') maps it back to
     a valid instruction in the darker blue oval,
     indicated by the dot in that oval,
     whose encoding is the one in the green oval.
     Based solely on the definition of @(tsee encdoding-validp),
     there is no guarantee that the valid instruction is unique
     (this is proved elsewhere, as explained shortly),
     but we know that @(tsee encode) takes us
     back to the initial encoding in the green oval.")
   (xdoc::p
    "The upper and lower `decode' arrows represent the function @(tsee decode),
     which is defined as the inverse of @(tsee encode).
     When applied to valid encodings in the darker green oval,
     @(tsee decode) coincides with @('encoding-valid-witness');
     when applied to invalid encodings in the lighter green oval
     that are not also in the darker green oval,
     @(tsee decode)) returns @('nil'), i.e. no instruction.")
   (xdoc::p
    "The upper and lower `decode' arrows also represent
     the executable decoding function @(tsee decodex),
     which is proved in @(tsee decode-is-decodex)
     to be equal to @(tsee decode).")
   (xdoc::p
    "From @(tsee decodex-of-encode) we also know that
     if we start with a valid instruction in the darker blue oval,
     and we encode obtaining a valid encoding in the darker gree oval,
     then if we apply @(tsee decode) or @(tsee decodex) (they are equal)
     we go back to the initial valid instruction.
     So @(tsee encode) is in fact injective,
     as explicated in @(tsee encode-injective),
     and the darker blue and darker green ovals
     are in bijective correspondence,
     with @(tsee encode) and @(tsee decode) (or @(tsee decodex))
     as the bijections between them.")))
